def test_in_on_any(results: Any) -> None:
    if results:
        assert 'key' in results, "key could be in results"
