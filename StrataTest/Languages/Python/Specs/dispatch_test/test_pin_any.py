class MyClient:
    def get_results(self) -> Any:
        try:
            return {}
        except Exception as e:
            return None

def test_in_on_any() -> None:
    c: MyClient = MyClient()
    results: Any = c.get_results()
    if results:
        assert 'key' in results, "key could be in results"
