use sa_lab::DataFrame;
use std::net::{TcpListener, TcpStream};

const ADDR: &str = "127.0.0.1:8080";

fn main() -> anyhow::Result<()> {
    let listener = TcpListener::bind(ADDR)?;
    for stream in listener.incoming() {
        handle_client(stream?)?;
    }
    Ok(())
}

fn handle_client(mut stream: TcpStream) -> Result<(), sa_lab::ParseError> {
    let frame = DataFrame::parse(&mut stream)?;
    println!("{frame:?}");
    Ok(())
}
