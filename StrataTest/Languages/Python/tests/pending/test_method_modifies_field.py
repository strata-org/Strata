class Account:
    balance: int

    def __init__(self, balance: int):
        self.balance = balance

    def deposit(self, amount: int):
        self.balance = self.balance + amount

    def withdraw(self, amount: int):
        self.balance = self.balance - amount

def test_oop_method_modifies_field():
    a = Account(100)
    a.deposit(50)
    assert a.balance == 150, "after deposit"
    a.withdraw(30)
    assert a.balance == 120, "after withdraw"

test_oop_method_modifies_field()
