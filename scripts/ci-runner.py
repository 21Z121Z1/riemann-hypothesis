#!/usr/bin/env python3
"""Prepare one ordinary GitHub Actions build runner; no fleet or cloud credentials."""
import argparse
import getpass
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import stat
import subprocess
import sys
import tarfile
import tempfile
import urllib.request

GROUP = "RiemannHypothesisBuild"
LABEL = "rh-build"
ORGANIZATION = "https://github.com/leanprover-community"
WORKFLOW = "leanprover-community/riemann-hypothesis/.github/workflows/build-pr.yml"
MAIN_REF = "refs/heads/main"
MAINTENANCE_REF = "refs/heads/infrastructure/byo-build-ci"
VERSION = "2.338.2"
# Official actions/runner v2.338.2 asset digests, read from GitHub's release API.
ARCHIVES = {
    "x64": "baebf204307bac6193480852732f0aba2ae97b6c5597c244f4d5558390147c40",
    "arm64": "670adb2f268fe21dcbb58b3db0e0aa9d5b3bddfe2c651481336e561ff86de945",
}
DEFAULT_DIRECTORY = Path.home() / ".local/share/riemann-build-runner"


def architecture():
    machine = platform.machine().lower()
    if machine in ("x86_64", "amd64"):
        return "x64"
    if machine in ("aarch64", "arm64"):
        return "arm64"
    raise ValueError(f"unsupported architecture: {machine}")


def private_file(path):
    """Read a credential without accepting a symlink, another owner, or public bits."""
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    try:
        info = os.fstat(fd)
        if (not stat.S_ISREG(info.st_mode) or info.st_uid != os.getuid()
                or stat.S_IMODE(info.st_mode) & 0o077):
            raise ValueError("credential file must be a regular file owned by you, mode 0600")
        with os.fdopen(fd, "r", closefd=False) as stream:
            value = stream.read(65537).strip()
        if not value or len(value) > 65536:
            raise ValueError("empty or oversized credential file")
        return value
    finally:
        os.close(fd)


def token(args):
    value = private_file(args.token_file) if args.token_file else (
        getpass.getpass("One-hour GitHub runner registration token: ")
        if sys.stdin.isatty() else sys.stdin.read(65537).strip())
    if not re.fullmatch(r"[A-Za-z0-9_.-]{8,4096}", value):
        raise ValueError("expected a short-lived runner registration/removal token")
    return value


def runner_directory(path):
    path = path.expanduser().absolute()
    if path.is_symlink():
        raise ValueError("runner directory must not be a symlink")
    if path.exists():
        info = path.stat()
        if info.st_uid != os.getuid() or stat.S_IMODE(info.st_mode) & 0o077:
            raise ValueError("runner directory must be owned by you, mode0700")
    return path


def doctor(args):
    if sys.platform != "linux":
        raise ValueError("Linux is required")
    existing = args.work_directory.expanduser().absolute()
    while not existing.exists():
        existing = existing.parent
    report = {
        "architecture": architecture(),
        "uid": os.getuid(),
        "free_disk_gib": round(shutil.disk_usage(existing).free / 2**30, 1),
        "commands": {name: shutil.which(name) for name in ("git", "cc", "python3", "bwrap")},
        "systemd_user": subprocess.run(
            ["systemctl", "--user", "show-environment"], stdout=subprocess.DEVNULL,
            stderr=subprocess.DEVNULL).returncode == 0 if shutil.which("systemctl") else False,
        "cgroup_v2": Path("/sys/fs/cgroup/cgroup.controllers").is_file(),
    }
    memory = Path("/proc/meminfo").read_text()
    report["physical_ram_gib"] = round(int(re.search(r"MemTotal:\s+(\d+)", memory)[1]) / 2**20, 1)
    if report["commands"]["bwrap"]:
        # This harmless probe checks namespaces/network, not the build harness's mount policy.
        probe = (
            "import errno,socket,sys; s=socket.socket(); s.settimeout(1); "
            "r=s.connect_ex(('1.1.1.1',9)); "
            "sys.exit(0 if r in (errno.ENETUNREACH,errno.EHOSTUNREACH,errno.EADDRNOTAVAIL) else 2)"
        )
        command = [report["commands"]["bwrap"], "--die-with-parent", "--new-session",
                   "--unshare-user", "--unshare-pid", "--unshare-ipc", "--unshare-net",
                   "--unshare-uts", "--ro-bind", "/", "/", "--tmpfs", "/home",
                   "--tmpfs", "/root", "--tmpfs", "/tmp", "--proc", "/proc",
                   "--dev", "/dev", "--chdir", "/tmp", str(Path(sys.executable).resolve()), "-c", probe]
        result = subprocess.run(command, capture_output=True, text=True, timeout=15)
        report["offline_bwrap"] = result.returncode == 0
        if result.returncode:
            report["bwrap_error"] = result.stderr.strip()[-2000:]
    else:
        report["offline_bwrap"] = False
    report["ready"] = (os.getuid() != 0 and all(report["commands"].values()) and report["offline_bwrap"]
                       and report["free_disk_gib"] >= args.minimum_disk_gib)
    print(json.dumps(report, indent=2))
    if not report["ready"]:
        raise ValueError("runner prerequisites failed; no host security settings were changed")


def install(args):
    if sys.platform != "linux" or os.getuid() == 0:
        raise ValueError("install as the dedicated unprivileged Linux runner account")
    directory = runner_directory(args.directory)
    if directory.exists() and any(directory.iterdir()):
        raise ValueError("installation directory must be absent or empty")
    arch = architecture()
    name = f"actions-runner-linux-{arch}-{VERSION}.tar.gz"
    url = f"https://github.com/actions/runner/releases/download/v{VERSION}/{name}"
    directory.mkdir(parents=True, mode=0o700, exist_ok=True)
    directory.chmod(0o700)
    with tempfile.TemporaryDirectory(prefix="rh-runner-install-") as temporary:
        archive = Path(temporary) / name
        request = urllib.request.Request(url, headers={"User-Agent": "RiemannHypothesisCI/1.0"})
        with urllib.request.urlopen(request, timeout=120) as response, archive.open("wb") as output:
            shutil.copyfileobj(response, output)
        with archive.open("rb") as stream:
            digest = hashlib.file_digest(stream, "sha256").hexdigest()
        if digest != ARCHIVES[arch]:
            raise ValueError("official runner archive SHA256 mismatch")
        with tarfile.open(archive, "r:gz") as bundle:
            bundle.extractall(directory, filter="data")
    print(f"Installed official GitHub runner {VERSION} ({arch}) in {directory}")
    print("Automatic runner updates remain enabled. Run doctor before registration.")


def check_policy(path, maintenance=False):
    """Require the operator's freshly fetched, owner-only GitHub group receipt."""
    policy = json.loads(private_file(path))
    if not isinstance(policy, dict):
        raise ValueError("runner-group policy receipt must be a JSON object")
    allowed = {f"{WORKFLOW}@{MAIN_REF}"}
    if maintenance:
        allowed.add(f"{WORKFLOW}@{MAINTENANCE_REF}")
    workflows = policy.get("selected_workflows")
    if (policy.get("name") != GROUP or policy.get("visibility") != "selected"
            or policy.get("restricted_to_workflows") is not True
            or policy.get("allows_public_repositories") is not True
            or not isinstance(workflows, list) or not workflows
            or not all(isinstance(item, str) for item in workflows)
            or not set(workflows) <= allowed
            or (not maintenance and set(workflows) != allowed)):
        raise ValueError("runner-group policy receipt must restrict this pool to the approved main workflow")


def register(args):
    if os.getuid() == 0:
        raise ValueError("register as the dedicated unprivileged runner account")
    directory = runner_directory(args.directory)
    if not (directory / "config.sh").is_file():
        raise ValueError("install the official runner first")
    if not args.remove and (directory / ".runner").exists():
        raise ValueError("already registered; stop and remove it explicitly before replacing")
    if not args.remove:
        if not args.policy_file:
            raise ValueError("--policy-file is required: obtain the restricted group's API receipt from the operator")
        check_policy(args.policy_file, args.maintenance)
    secret = token(args)
    command = [str(directory / "config.sh")]
    if args.remove:
        command += ["remove", "--unattended", "--token", secret]
    else:
        if not re.fullmatch(r"[A-Za-z0-9_.-]{1,64}", args.name):
            raise ValueError("runner name must contain only letters, digits, dots, hyphens or underscores")
        command += ["--unattended", "--url", ORGANIZATION, "--token", secret,
                    "--runnergroup", GROUP, "--labels", LABEL, "--name", args.name,
                    "--work", "_work"]
        if args.ephemeral:
            command.append("--ephemeral")
    # Never print command: GitHub's official config interface takes the short-lived token in argv.
    subprocess.run(command, cwd=directory, check=True)
    for name in (".credentials", ".credentials_rsaparams", ".runner"):
        path = directory / name
        if path.is_file():
            path.chmod(0o600)
    if not args.remove:
        print("Registered one job slot. The runner account must receive only the approved main workflow.")


def systemd_quote(value):
    if "\n" in value or "\r" in value:
        raise ValueError("newline in service path")
    return '"' + value.replace("%", "%%").replace("\\", "\\\\").replace('"', '\\"') + '"'


def unit(args):
    directory = runner_directory(args.directory)
    # WorkingDirectory is one literal path, unlike ExecStart's word parser.
    # Quoting it makes the quote part of the path and fails validation.
    path = str(directory)
    if "\\" in path or any(ord(char) < 32 or ord(char) == 127 for char in path):
        raise ValueError("unsupported control character or backslash in service working directory")
    path = path.replace("%", "%%")
    run = systemd_quote(str(directory / "run.sh"))
    print(f"""[Unit]
Description=Riemann hypothesis trusted build runner
After=network-online.target

[Service]
WorkingDirectory={path}
ExecStart={run}
Restart=on-failure
RestartSec=10
KillMode=control-group
TimeoutStopSec=120
UMask=0077
LimitNOFILE=65536
Nice=10
Delegate=yes

[Install]
WantedBy=default.target""")


def run_jit(args):
    if os.getuid() == 0:
        raise ValueError("run as the dedicated unprivileged runner account")
    directory = runner_directory(args.directory)
    check_policy(args.policy_file, args.maintenance)
    value = private_file(args.config_file)
    # The operator obtains this one-job credential from GitHub's generate-jitconfig API.
    # This does not mint a new credential or implement an unattended registration broker.
    subprocess.run([str(directory / "run.sh"), "--jitconfig", value], cwd=directory, check=True)


def aws_user_data(args):
    print("""#cloud-config
# Debian 12/13 or another compatible apt-based image. No registration credential here.
package_update: true
packages:
  - ca-certificates
  - git
  - curl
  - python3
  - bubblewrap
  - build-essential
  - libicu-dev
  - libkrb5-3
  - libssl-dev
  - zlib1g
users:
  - default
  - name: rh-ci
    gecos: Riemann hypothesis build runner
    lock_passwd: true
    shell: /bin/bash
runcmd:
  - [install, -d, -m, '0700', -o, rh-ci, -g, rh-ci, /var/lib/rh-ci]
  - [loginctl, enable-linger, rh-ci]
# Use a 1 TiB encrypted root volume. Install/register after trusted operator access.
# No AWS instance profile, inbound listener, public registration token, or sysctl changes.
""")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    commands = parser.add_subparsers(dest="command", required=True)
    check = commands.add_parser("doctor", help="probe prerequisites without changing host settings")
    check.add_argument("--work-directory", type=Path, default=Path.home())
    check.add_argument("--minimum-disk-gib", type=int, default=250)
    check.set_defaults(function=doctor)
    download = commands.add_parser("install", help="install checksum-pinned official GitHub runner")
    download.add_argument("--directory", type=Path, default=DEFAULT_DIRECTORY)
    download.set_defaults(function=install)
    configure = commands.add_parser("register", help="register with an operator-issued one-hour token")
    configure.add_argument("--directory", type=Path, default=DEFAULT_DIRECTORY)
    configure.add_argument("--name", default=platform.node().split(".")[0])
    configure.add_argument("--token-file", type=Path, help="private mode0600 file; otherwise stdin/prompt")
    configure.add_argument("--policy-file", type=Path, help="required mode0600 fresh GitHub runner-group API receipt")
    configure.add_argument("--maintenance", action="store_true", help="also accept the exact trusted infrastructure/byo-build-ci branch during operator acceptance")
    configure.add_argument("--ephemeral", action="store_true", help="one job only; requires new enrollment afterward")
    configure.add_argument("--remove", action="store_true", help="use a fresh removal token; stop service first")
    configure.set_defaults(function=register)
    service = commands.add_parser("systemd-unit", help="print a persistent user service; does not install/start it")
    service.add_argument("--directory", type=Path, default=DEFAULT_DIRECTORY)
    service.set_defaults(function=unit)
    jit = commands.add_parser("run-jit", help="run one operator-issued JIT job; no automatic replenishment")
    jit.add_argument("--directory", type=Path, default=DEFAULT_DIRECTORY)
    jit.add_argument("--config-file", required=True, type=Path)
    jit.add_argument("--policy-file", required=True, type=Path)
    jit.add_argument("--maintenance", action="store_true")
    jit.set_defaults(function=run_jit)
    cloud = commands.add_parser("aws-user-data", help="print minimal credential-free cloud-init; does not provision AWS")
    cloud.set_defaults(function=aws_user_data)
    args = parser.parse_args()
    args.function(args)


if __name__ == "__main__":
    try:
        main()
    except (OSError, ValueError, subprocess.SubprocessError) as error:
        # CalledProcessError embeds argv, which can include registration/JIT credentials.
        if isinstance(error, subprocess.SubprocessError):
            sys.exit("Runner command failed; see its preceding diagnostics (credentials omitted).")
        sys.exit(str(error))
