import test_helper
import json

def main():
    # Using config-c which doesn't support AI service
    bar_client = test_helper.create_client('bar', 'config-c')

    try:
        response: str = test_helper.invoke(
            client=bar_client,
            arg_str='bar',
            input_data=json.dumps({
                'inputText': 'Hello, world!',
                'config': {
                    'myInt': 50,
                    'myFloat': 0.7
                }
            })
        )
        print("Success:", response)
    except Exception as e:
        print(f"Error: {e}")

if __name__ == "__main__":
    main()
