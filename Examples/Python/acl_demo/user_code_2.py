import acl

# --- Symbolic: does the logic hold for ANY role? ---

# The solver uses the if-guard to prove delete is safe,
# but flags read_resource — an arbitrary role might not be valid.
def conditional_delete(role: str) -> bool:
    client = acl.connect("access_control")
    client.read_resource(role=role, resource_id="data/report")
    if role == "admin":
        client.delete_resource(role=role, resource_id="tmp/cache")
    return True