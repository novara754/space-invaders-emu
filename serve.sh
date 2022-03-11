set -xe
wasm-pack build --target web
python3 -m http.server -b 172.18.162.13 8080
