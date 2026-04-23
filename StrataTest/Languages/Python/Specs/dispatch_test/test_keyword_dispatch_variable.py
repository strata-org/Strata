import servicelib

def keyword_dispatch_variable(svc: str) -> bool:
    client = servicelib.connect(service_name=svc)
    return True
