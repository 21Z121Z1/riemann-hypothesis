#!/usr/bin/env python3
"""Credential and process-boundary checks; no GitHub/AWS calls or registration."""
import importlib.util
import os
import json
from pathlib import Path
import subprocess
import shutil
import sys
import tempfile
import unittest

SCRIPT = Path(__file__).with_name("ci-runner.py")
spec = importlib.util.spec_from_file_location("ci_runner", SCRIPT)
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


class RunnerChecks(unittest.TestCase):
    def test_private_credentials_reject_public_files_and_symlinks(self):
        with tempfile.TemporaryDirectory() as name:
            path = Path(name) / "credential"
            path.write_text("testcredential")
            path.chmod(0o600)
            self.assertEqual(runner.private_file(path), "testcredential")
            path.chmod(0o644)
            with self.assertRaises(ValueError):
                runner.private_file(path)
            path.chmod(0o600)
            link = path.with_name("link")
            link.symlink_to(path)
            with self.assertRaises(OSError):
                runner.private_file(link)

    @unittest.skipIf(os.getuid() == 0, "registration correctly refuses root")
    def test_failed_official_config_does_not_echo_token_in_error(self):
        with tempfile.TemporaryDirectory() as name:
            root = Path(name)
            root.chmod(0o700)
            config = root / "config.sh"
            config.write_text("#!/bin/sh\nexit 7\n")
            config.chmod(0o700)
            token = root / "registration-token"
            secret = "not-a-real-registration-token-1234"
            token.write_text(secret)
            token.chmod(0o600)
            policy = root / "policy.json"
            policy.write_text(json.dumps({
                "name": runner.GROUP, "visibility": "selected", "allows_public_repositories": True,
                "restricted_to_workflows": True,
                "selected_workflows": [f"{runner.WORKFLOW}@{runner.MAIN_REF}"]}))
            policy.chmod(0o600)
            result = subprocess.run(
                [sys.executable, str(SCRIPT), "register", "--directory", str(root),
                 "--token-file", str(token), "--policy-file", str(policy)], capture_output=True, text=True)
            self.assertNotEqual(result.returncode, 0)
            self.assertNotIn(secret, result.stdout + result.stderr)
            self.assertIn("credentials omitted", result.stderr)

    def test_policy_rejects_branch_or_repository_expansion(self):
        with tempfile.TemporaryDirectory() as name:
            path = Path(name) / "policy.json"
            data = {"name": runner.GROUP, "visibility": "selected", "allows_public_repositories": True,
                    "restricted_to_workflows": True,
                    "selected_workflows": [f"{runner.WORKFLOW}@{runner.MAIN_REF}"]}
            path.write_text(json.dumps(data)); path.chmod(0o600)
            runner.check_policy(path)
            data["selected_workflows"].append(f"{runner.WORKFLOW}@refs/pull/123/head")
            path.write_text(json.dumps(data))
            with self.assertRaises(ValueError):
                runner.check_policy(path, maintenance=True)
            data["selected_workflows"] = [f"{runner.WORKFLOW}@{runner.MAINTENANCE_REF}"]
            path.write_text(json.dumps(data))
            with self.assertRaises(ValueError):
                runner.check_policy(path)
            runner.check_policy(path, maintenance=True)

    def test_unit_rejects_newline_and_escapes_systemd_specifiers(self):
        with self.assertRaises(ValueError):
            runner.systemd_quote("/runner\nExecStart=malicious")
        self.assertEqual(runner.systemd_quote('/runner/%h/"quoted"'),
                         '"/runner/%%h/\\"quoted\\""')


    @unittest.skipUnless(shutil.which("systemd-analyze"), "systemd-analyze is not installed")
    def test_generated_unit_passes_real_systemd_parser(self):
        with tempfile.TemporaryDirectory() as name:
            directory = Path(name) / 'runner with spaces'
            directory.mkdir(mode=0o700)
            executable = directory / "run.sh"
            executable.write_text("#!/bin/sh\nexit 0\n")
            executable.chmod(0o700)
            contents = subprocess.check_output(
                [sys.executable, str(SCRIPT), "systemd-unit", "--directory", str(directory)], text=True)
            service = Path(name) / "rh-runner-test.service"
            service.write_text(contents)
            result = subprocess.run(["systemd-analyze", "--user", "verify", str(service)],
                                    capture_output=True, text=True)
            self.assertEqual(result.returncode, 0, result.stderr)


if __name__ == "__main__":
    unittest.main()
