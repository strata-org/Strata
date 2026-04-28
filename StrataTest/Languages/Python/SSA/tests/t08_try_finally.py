# Test: Try/finally, isDefined pattern for exception vs normal path

def work():
    pass

def cleanup():
    pass

# Try/finally — cleanup runs on both paths
try:
    work()
finally:
    cleanup()

# Try/except/finally
try:
    x = 1
except:
    x = 0
finally:
    cleanup()
