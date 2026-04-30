class Classifier:
    threshold: int

    def __init__(self, threshold: int):
        self.threshold = threshold

    def classify(self, val: int) -> str:
        if val >= self.threshold:
            return "high"
        return "low"

def test_oop_method_conditional_return():
    c = Classifier(10)
    r1: str = c.classify(15)
    assert r1 == "high", "above threshold"
    r2: str = c.classify(5)
    assert r2 == "low", "below threshold"

test_oop_method_conditional_return()
