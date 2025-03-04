## About the Project

Sample parser in Rust with a TCP server serving as an example

## Usage

Start server to receive local connections on port `8080`:
```sh
cargo run --example server
```

Send commands (e.g. using `netcat`):
```sh
echo -e -n '\x16\x1\x6\x0\x0\x0\x1\x2\x3\x4\x5\x6' | nc 127.0.0.1 8080
```

Server prints results to console and exits once invalid input has 
been received: 
```
DataFrame { kind: 1, size: 3, data: [1, 2, 3] }
DataFrame { kind: 1, size: 5, data: [1, 2, 3, 4, 5] }
DataFrame { kind: 1, size: 6, data: [1, 2, 3, 4, 5, 6] }
Error: Insufficient number of bytes in a stream (expected 7, got 6)
```

## Message Format


| Field name | Start | Kind        | Size | Data       |
|------------|-------|-------------|------|------------|
| Data type  | u8    | u8          | u32  | [u8; Size] |
| Value      | 22    | StringValue | xxx  | [..., ...] |

- `Start` - Each message starts with SYN (22)
- `Kind` - The `Kind` of the data stored in the `Data` field, refer to
- `Size` - The length of the `Data` field in bytes
- `Data` - Data structured depending on it `Kind`
