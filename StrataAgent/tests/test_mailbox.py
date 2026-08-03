"""Deterministic tests for the persistent email-style mailbox.

Covers the storage model (_channels.Mailbox) and the MCP tool surface
(_messaging: send_message, pull tools, wait_for_reply) plus the push-notification
logic. No LLM, no network — pure in-process.

Run:
  PYTHONPATH=StrataAgent <py> tests/test_mailbox.py
"""

from __future__ import annotations

import asyncio
import tempfile
from pathlib import Path

from strataswarm._channels import ChannelBus, Mailbox
from strataswarm._messaging import create_messaging_server, render_mail, render_header


# ── helpers ──────────────────────────────────────────────────────────────────

def _tools(server):
    """Map tool name -> handler callable for a messaging sdk server.

    Handlers live on the server's `instance` object (not a top-level dict key)
    so they never reach the subprocess transport's json.dumps of mcp_servers.
    """
    inst = server.get("instance")
    return dict(getattr(inst, "_tool_handlers", {}))


async def _text(handler, **kwargs):
    res = await handler({**kwargs})
    return res["content"][0]["text"]


def mk_bus(tmp):
    bus = ChannelBus()
    bus.bind_mailbox_file(Path(tmp) / "mailbox.jsonl")
    return bus


# ── Mailbox unit tests ─────────────────────────────────────────────────────

def test_mailbox_core():
    d = tempfile.mkdtemp()
    p = Path(d) / "mailbox.jsonl"
    mb = Mailbox(); mb.bind_file(p)

    e1 = mb.deliver("proof_guide", "SearchAgent", "What is the signature of Block.mk?")
    assert e1.msg_id == 1 and e1.thread_id == 1 and e1.in_reply_to is None
    assert e1.subject == "What is the signature of Block.mk?"

    e2 = mb.deliver("SearchAgent", "proof_guide", "Block.mk : Nat -> Block")
    assert e2.thread_id == 1 and e2.in_reply_to == 1  # inferred from open exchange
    assert e2.subject == e1.subject

    e3 = mb.deliver("proof_guide", "SearchAgent", "second question", subject="lengths")
    assert e3.thread_id == 3 and e3.subject == "lengths" and e3.in_reply_to is None  # explicit subject => new thread

    assert mb.unread_count("SearchAgent") == 2 and mb.unread_count("proof_guide") == 1
    assert [x.msg_id for x in mb.unread_entries("SearchAgent")] == [1, 3]
    assert mb.oldest_unread("SearchAgent").msg_id == 1
    mb.mark_read("SearchAgent", 1)
    assert mb.unread_count("SearchAgent") == 1

    ents, total = mb.thread_slice(1)
    assert total == 2 and [x.msg_id for x in ents] == [1, 2]
    ents2, total2 = mb.thread_slice(2, 0, 1)  # resolve by msg_id inside the thread
    assert total2 == 2 and [x.msg_id for x in ents2] == [1]

    assert [x.msg_id for x in mb.from_sender("SearchAgent", "proof_guide", 1)] == [3]
    mb.close()
    print("  test_mailbox_core OK")


def test_reload_assumes_read_and_resumes_ids():
    d = tempfile.mkdtemp()
    p = Path(d) / "mailbox.jsonl"
    mb = Mailbox(); mb.bind_file(p)
    mb.deliver("a", "b", "one"); mb.deliver("b", "a", "two"); mb.close()

    mb2 = Mailbox(); mb2.bind_file(p)
    assert mb2.unread_count("a") == 0 and mb2.unread_count("b") == 0  # everything read
    assert len(mb2.inbox("b")) == 1 and len(mb2.inbox("a")) == 1
    e = mb2.deliver("a", "b", "three")
    assert e.msg_id == 3  # resumed at max+1
    mb2.close()
    print("  test_reload_assumes_read_and_resumes_ids OK")


def test_torn_write_tolerance():
    d = tempfile.mkdtemp()
    p = Path(d) / "mailbox.jsonl"
    mb = Mailbox(); mb.bind_file(p)
    mb.deliver("a", "b", "one"); mb.deliver("a", "b", "two"); mb.close()
    with open(p, "a") as f:
        f.write('{"msg_id": 99, "thread_id": 99, "sen')  # crash mid-append
    mb2 = Mailbox(); mb2.bind_file(p)
    ids = [e.msg_id for e in mb2.inbox("b")]
    assert ids == [1, 2] and 99 not in ids  # torn tail skipped, history intact
    mb2.close()
    print("  test_torn_write_tolerance OK")


# ── MCP tool-surface tests ──────────────────────────────────────────────────

async def test_tool_surface():
    d = tempfile.mkdtemp()
    bus = mk_bus(d)
    guide = create_messaging_server("proof_guide", bus, known_agents=["SearchAgent"])
    tools = _tools(guide)
    if not tools:
        print("  test_tool_surface SKIPPED (could not introspect sdk tool registry)")
        return

    send = tools["send_message"]
    # guide -> SearchAgent (delivery status, not a reply)
    txt = await _text(send, to="SearchAgent", message="sig of Block.mk?", subject="block sig")
    assert "Delivered to 'SearchAgent'" in txt and "#1" in txt, txt

    # SearchAgent replies -> lands in guide's mailbox
    bus.mailbox.deliver("SearchAgent", "proof_guide", "Block.mk : Nat -> Block", in_reply_to=1)

    # list_all_unread_mail: header only, does not mark read
    txt = await _text(tools["list_all_unread_mail"])
    assert "1 unread" in txt and "RE: block sig" in txt
    assert bus.mailbox.unread_count("proof_guide") == 1  # still unread after browse

    # see_last_unread_mail: full body, marks read
    txt = await _text(tools["see_last_unread_mail"])
    assert "Block.mk : Nat -> Block" in txt and "RE: block sig" in txt
    assert bus.mailbox.unread_count("proof_guide") == 0

    # get_thread: both sides, sliceable
    txt = await _text(tools["get_thread"], id=1)
    assert "sig of Block.mk?" in txt and "Block.mk : Nat -> Block" in txt

    # wait_for_reply fast path: an already-waiting unread returns immediately
    bus.mailbox.deliver("SearchAgent", "proof_guide", "also see Block.size", in_reply_to=1)
    txt = await _text(tools["wait_for_reply"], sender="SearchAgent", timeout=1)
    assert "Block.size" in txt

    # wait_for_reply timeout path: no message from that sender
    txt = await _text(tools["wait_for_reply"], sender="Nobody", timeout=0.2)
    assert "No reply from 'Nobody'" in txt
    print("  test_tool_surface OK")


async def test_reply_only_has_no_pull_tools():
    """reply_only agents (e.g. SearchAgent) get ONLY send_message + get_time — the
    pull tools are gated off; they receive via push-inline instead."""
    d = tempfile.mkdtemp()
    bus = mk_bus(d)
    srv = create_messaging_server(
        "SearchAgent", bus, known_agents=["proof_guide"], reply_only_mode=True
    )
    tools = _tools(srv)
    if not tools:
        print("  test_reply_only_has_no_pull_tools SKIPPED (no tool introspection)")
        return
    assert "send_message" in tools and "get_time" in tools
    for t in ("list_recent_messages", "see_last_unread_mail", "get_thread",
              "wait_for_reply", "get_messages_by_sender", "list_all_unread_mail"):
        assert t not in tools, f"reply_only should not expose {t}"
    print("  test_reply_only_has_no_pull_tools OK")


def test_render():
    d = tempfile.mkdtemp()
    mb = Mailbox(); mb.bind_file(Path(d) / "m.jsonl")
    root = mb.deliver("proof_guide", "SearchAgent", "q body", subject="topic")
    reply = mb.deliver("SearchAgent", "proof_guide", "a body", in_reply_to=root.msg_id)
    r = render_mail(reply, mb)
    assert "Subject: RE: topic" in r and '↳ Replying to #1 "topic"' in r and "a body" in r
    # no RE: on a fresh message
    assert render_mail(root, mb).count("RE:") == 0
    h = render_header(reply, unread=True)
    assert h.startswith("● ") and "RE: topic" in h
    mb.close()
    print("  test_render OK")


if __name__ == "__main__":
    test_mailbox_core()
    test_reload_assumes_read_and_resumes_ids()
    test_torn_write_tolerance()
    test_render()
    asyncio.run(test_tool_surface())
    asyncio.run(test_reply_only_has_no_pull_tools())
    print("ALL MAILBOX TESTS PASSED")
