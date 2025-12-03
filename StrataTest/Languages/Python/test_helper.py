"""Test helper functions for Strata Python language testing."""

from typing import Dict, Any

def procedure(req_name: str, opt_name: str | None) -> None:
    """Test procedure with required and optional parameters.
    
    Args:
        req_name: Required name parameter, must be "foo"
        opt_name: Optional name parameter, must be None or "bar"
    """
    assert req_name == "foo"
    assert opt_name is None or opt_name == "bar"

def create_client(client_type: str, client_config: str) -> Any:
    """Create a test client with specified type and configuration.
    
    Args:
        client_type: Type of client, must be 'foo' or 'bar'
        client_config: Configuration string for the client
        
    Returns:
        Dictionary containing client type and configuration
    """
    assert client_type in ['foo', 'bar']
    return {'client_type': client_type, 'client_config': client_config}

def upload(client: Any, folder: str, key: str, payload: Any, encryption_type: str | None = None, encryption_key_id: str | None = None) -> Dict[str, Any]:
    """Upload payload to specified folder with optional encryption.
    
    Args:
        client: Client object for upload
        folder: Target folder name (3-63 chars, lowercase, specific format rules)
        key: Upload key identifier
        payload: Data to upload
        encryption_type: Optional encryption method
        encryption_key_id: Optional encryption key ID (requires encryption_type)
        
    Returns:
        Dictionary with upload status
    """
    assert len(folder) >= 3 and len(folder) <= 63
    assert folder.replace('-', '').replace('.', '').islower()
    assert not folder.startswith('-') and not folder.startswith('.')
    assert not folder.startswith('xn--')
    assert not folder.endswith('-alias')
    if encryption_key_id is not None:
        assert encryption_type is not None
    return {'status': 'success'}

def invoke(client: Any, model_id: str, input_data: str) -> str:
    """Invoke model with input data using specified client.
    
    Args:
        client: Client object (config cannot be 'config-c')
        model_id: Identifier for the model to invoke
        input_data: Input data for model processing
        
    Returns:
        Model response string
    """
    assert client['client_config'] != 'config-c'
    return 'model response'