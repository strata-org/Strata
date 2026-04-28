# Pending: non-finite float literals (inf, nan) are translated to Hole
# because Decimal cannot represent them. Assertions are inconclusive.

def test_inf():
    x: float = 1e309  # overflow to inf
    assert x > 0

def test_neg_inf():
    x: float = -1e309  # overflow to -inf
    assert x < 0

test_inf()
test_neg_inf()
