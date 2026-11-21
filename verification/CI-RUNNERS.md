# Contribute a runner
Send Kim your CPU/RAM, architecture, free SSD space, and availability.
Linux only; 128 GiB RAM and 1 TiB SSD recommended, 250 GiB free required.
Use a dedicated account: jobs run untrusted PR code in an offline sandbox.
Install Git, Python 3.11+, a C compiler, Bubblewrap, and Elan.
Download [ci-runner.py](https://raw.githubusercontent.com/leanprover-community/riemann-hypothesis/main/scripts/ci-runner.py).
Run `python3 ci-runner.py doctor` and send Kim its output.
Then run `python3 ci-runner.py install`.
Kim will send private enrollment files and the final start command.
You do not need a GitHub PAT or Cloudflare credentials.
