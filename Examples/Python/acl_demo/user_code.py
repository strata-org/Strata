import acl

# --- Concrete: specific usage, everything passes ---

def admin_workflow() -> bool:
    client = acl.connect("access_control")
    client.read_resource(role="admin", resource_id="secrets/key")
    client.write_resource(role="admin", resource_id="config/settings", content="timeout=30")
    client.delete_resource(role="admin", resource_id="tmp/cache")
    return True