# Build runners

The `RiemannHypothesisBuild` GitHub runner group and `rh-build` label form one
pool for ordinary cached `lake build` jobs. Start with **one runner per host**;
the official runner accepts one job at a time. AWS and volunteer machines use
the same enrollment and workflow. These jobs do not export declarations or run
Comparator.

## Trust boundary

Before issuing a registration token, an organization administrator must restrict
the group to this repository and exactly
`leanprover-community/riemann-hypothesis/.github/workflows/build-pr.yml@refs/heads/main`.
The operator must verify `restricted_to_workflows: true` and the exact
`selected_workflows` value using GitHub's runner-group API. A label or a selected
repository alone does not enforce this boundary. Do not enroll a persistent host
if the organization's plan/API cannot enforce workflow restrictions.

The trusted workflow and build harness come from trusted `main`. Candidate PR
files execute only in the harness's offline Bubblewrap namespace. Candidate
checkouts, Lake configuration, actions, and shell scripts must never become host
setup commands. The harness hides the runner account's home, runner credentials,
Git credentials, host sockets and writable cgroups, and exposes only its explicit
build inputs and scratch. Job scratch is removed after each build. Persistent
host-side caches and the official agent remain owned by the trusted runner
account.

Use a dedicated unprivileged Unix account, such as `rh-ci`, without sudo or
unrelated personal credentials. The GitHub agent, its credentials and its setup
code live in that private account, outside candidate mounts. The agent itself is
not a sandbox: group restrictions and the trusted harness are both required.
This setup intentionally grants no cache-upload credential to build runners;
publishing uses the separately trusted workflow.

The [TauCetiFleet native runner model](https://github.com/TauCetiProject/TauCetiFleet/blob/main/docs/native-runners.md)
also separates trusted setup from offline candidate computation. Its disposable
OS images, broker/JIT enrollment, controller and slot-recovery machinery are not
needed for this single-slot setup and are not deployed here. This agent persists
between jobs; only candidate workspaces are disposable.

## Build and publication flow

`Build PR` resolves the proposed merge commit on a hosted runner, then sends it
to this pool. A warm build restores the original proof cache and the latest
available ancestor cache before running stock Lake. It publishes completed
modules even when another module fails, so a retry can retain completed work.
The workflow finishes active builds rather than cancelling them on every update.

`Publish CI cache` runs separately on a GitHub-hosted runner, validates the build
identity and opaque output hashes, and uploads only new artifacts. Its R2 token
is an environment secret in `ci-cache-publish`, restricted to main. AWS and
volunteer build hosts never receive it. Full successful maps are indexed by
source/configuration inputs: equivalent PRs skip compilation, and merging to
main promotes the same outputs without rebuilding them. No exporter or
Comparator is run.

Compiler and dependency revisions remain pinned. A PR that changes those inputs
requires preparing the new trusted toolchain/dependency cache first; CI fails
rather than executing candidate dependency setup on a volunteer host.

The public cache **includes outputs from untrusted PRs and volunteer machines**.
Hash and provenance checks protect transport and cache indexing; they do not
verify proofs. Users who need independent verification must perform a clean
build without this cache.

`lake exe cache get` looks for a successful cache matching the checked-out source,
Lake configuration, dependencies and toolchain, then falls back to the original
published cache. It needs no per-user configuration.

## Host preparation

Use Linux with working unprivileged user, mount, PID and network namespaces,
Bubblewrap, Git, Python 3.11 or newer, a C compiler, and the pinned stock Lean
toolchain. A functioning user systemd manager provides unattended operation.
Cgroup v2 is reported by `doctor`; resource limits belong to the build harness.

The initial AWS host should have 128–256 GiB RAM and a 1 TiB encrypted disk, with
one job at a time and modest build concurrency. Cached Main validation used about
4.2 GiB RSS, but rebuilding changed modules can require more. Keep at least
250 GiB free for the proof artifacts, candidate scratch and preparation. The
1 TiB disk supplies operational headroom, not a proof-size requirement.

Run from a trusted checkout as the dedicated runner account:

```sh
python3 scripts/ci-runner.py doctor --work-directory "$HOME"
python3 scripts/ci-runner.py install
```

Installation verifies the official GitHub Actions runner release's SHA256. The
initial version is pinned in the script; official runner automatic updates stay
enabled. The [release source](https://github.com/actions/runner/releases/tag/v2.338.2)
supplies x64 and arm64 artifacts. If the .NET runner reports missing native
libraries, the host administrator can run the downloaded official
`bin/installdependencies.sh`; the runner account itself has no sudo access.

`doctor` makes no sysctl, AppArmor or host security changes. It executes a harmless
offline namespace probe as the actual unprivileged user. A failure is a setup
failure, not permission to run candidate code without isolation. Debian 12/13 is
a straightforward initial image. Ubuntu's user-namespace policy can require
additional administrator configuration, which this script does not perform.

## Persistent volunteer enrollment

The operator creates/verifies the restricted group, then issues an organization
runner registration token from their own authenticated machine:

```sh
umask 077
gh api orgs/leanprover-community/actions/runner-groups/GROUP_ID > group-policy.json
gh api --method POST \
  orgs/leanprover-community/actions/runners/registration-token --jq .token
```

Transfer the freshly fetched `group-policy.json` and **one-hour registration
token**, not a PAT or GitHub App key, to the volunteer. Both files must be owned
by the runner user and mode 0600. The policy receipt is an operator assertion,
not a signed attestation: the operator must obtain it directly from GitHub and
verify the group's selected repositories as well. Registration fails closed if
the receipt permits a PR ref, another repository/workflow, or unrestricted jobs.
Do not paste the token into a shell command, cloud-init, workflow log, or committed
file. The volunteer can enter it at the hidden prompt:

```sh
python3 scripts/ci-runner.py register --name my-rh-build-host \
  --policy-file group-policy.json
```

For unattended enrollment, `--token-file FILE` requires a regular, owner-only
mode-0600 file; remove it after successful enrollment. Registration selects the
organization URL, group and label itself. It refuses to silently replace an
existing identity. The resulting GitHub runner identity persists locally under
a mode-0700 runner directory, with owner-only credential files. No cloud
credential or broad GitHub token is needed on the volunteer's machine.

Enable a user service:

```sh
mkdir -p ~/.config/systemd/user
python3 scripts/ci-runner.py systemd-unit \
  > ~/.config/systemd/user/rh-build-runner.service
systemctl --user daemon-reload
systemctl --user enable --now rh-build-runner.service
```

The administrator must enable lingering for this dedicated account if its user
manager otherwise exits at logout: `loginctl enable-linger rh-ci`. Registration
then remains available across jobs and reboots without repeated operator tokens.
Observe it with `systemctl --user status rh-build-runner` and
`journalctl --user -u rh-build-runner`. Stop or disable the service to withdraw
the host; an administrator can revoke its identity in the GitHub group. To
remove the local registration, stop it first and use `register --remove` with a
fresh GitHub runner-removal token.

## One-job alternatives

`register --ephemeral` makes the official runner unregister after one job. It
then needs another operator-issued registration. `run-jit --config-file FILE`
starts one operator-issued GitHub JIT configuration; the file must be owner-only.
Both modes still require `--policy-file group-policy.json`.
Neither mode is an unattended volunteer pool by itself. Replenishing those
credentials requires an operator loop or an actual broker/controller. This
implementation does not introduce such a service or retain a PAT to emulate it.

During initial operator acceptance only, `--maintenance` additionally accepts the
exact same workflow on `refs/heads/infrastructure/byo-build-ci`, if GitHub's
fresh group receipt allows it. Arbitrary branch refs and PR refs remain rejected.
Remove that temporary group permission before production volunteer enrollment;
ordinary registration accepts only the main workflow.

## Minimal AWS bootstrap

The script prints reviewable, credential-free cloud-init:

```sh
python3 scripts/ci-runner.py aws-user-data > rh-runner-cloud-init.yaml
```

The cloud administrator selects an apt-based image, encrypted 1 TiB disk, account,
region, instance size and ordinary management access. Cloud-init installs basic
tools and creates the private `rh-ci` account with lingering. It does not create
instances, alter quotas/SCPs, register GitHub runners, install a privileged
container daemon, or embed credentials. After provisioning, use the same trusted
checkout, doctor, install and registration commands as for a volunteer. No
inbound build-job port is needed: the GitHub runner initiates its connection.

The dedicated RH AWS account is `419423654034`; the `riemann-hypothesis` local
operator profile assumes its organization access role. An SCP can deny an
otherwise permitted API; service-quota changes and infrastructure provisioning
remain operator actions, separate from this script and from build jobs.

## Checks

```sh
python3 scripts/test_ci_runner.py
python3 scripts/ci-runner.py doctor --minimum-disk-gib 0
```

The unit checks cover credential-file access, accidental credential disclosure on
failed registration, and service-path injection. Doctor's network probe was
exercised locally as an unprivileged user with Bubblewrap; installation and
registration are explicit operator actions and are not performed by these tests.

GitHub documents [registration](https://docs.github.com/en/actions/how-tos/manage-runners/self-hosted-runners/add-runners),
[one-hour runner tokens](https://docs.github.com/en/rest/actions/self-hosted-runners#create-a-registration-token-for-an-organization),
and [selected-workflow runner-group restrictions](https://docs.github.com/en/enterprise-cloud%40latest/actions/how-tos/manage-runners/self-hosted-runners/manage-access).
