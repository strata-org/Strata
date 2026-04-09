import acl

def valid_admin_access() -> bool:
    client = acl.connect("access_control")
    client.read_resource(role="admin", resource_id="secrets/api-key")       # expect: pass
    client.write_resource(role="admin", resource_id="config/settings", content="timeout=30")  # expect: pass
    client.delete_resource(role="admin", resource_id="tmp/stale-cache")     # expect: pass
    return True

def valid_editor_access() -> bool:
    client = acl.connect("access_control")
    client.read_resource(role="editor", resource_id="docs/guide")           # expect: pass
    client.write_resource(role="editor", resource_id="docs/guide", content="updated")  # expect: pass
    return True

def valid_viewer_access() -> bool:
    client = acl.connect("access_control")
    client.read_resource(role="viewer", resource_id="public/faq")           # expect: pass
    return True

def invalid_viewer_write() -> bool:
    client = acl.connect("access_control")
    client.write_resource(role="viewer", resource_id="docs/guide", content="hacked")  # expect: FAIL (viewer cannot write)
    return True
