def procedure (req_name: str, opt_name : str | None) -> None:
    assert req_name == "foo"
    assert opt_name is None or opt_name == "bar"