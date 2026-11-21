"""Check one exact Fewest Nets routing table with bounded Lean concurrency."""

import argparse
from concurrent.futures import ThreadPoolExecutor, as_completed
import os
from pathlib import Path
import subprocess


def module_name(path):
    return ".".join(path.with_suffix("").parts)


def check_module(lake, module, log):
    env = dict(os.environ)
    env.setdefault("LEAN_NUM_THREADS", "2")
    with log.open("wb") as output:
        result = subprocess.run(
            [lake, "--no-ansi", "--quiet", "build", f"+{module}"],
            stdout=output,
            stderr=subprocess.STDOUT,
            env=env,
            check=False,
        )
    return result.returncode


def audit_endpoint(lake, frequency, logs):
    theorem = f"Unfoldings.SpatialFolding.ConvexBoundary.exists_netPartition_lt_q{frequency}"
    source = logs / "AuditEndpoint.lean"
    source.write_text(
        f"""module

import Unfoldings.FewestNets.PaperFrequency{frequency}
import Lean.Util.CollectAxioms

open Lean in
run_cmd do
  let allowed := #[``propext, ``Classical.choice, ``Quot.sound]
  for dependency in (← collectAxioms ``{theorem}) do
    unless allowed.contains dependency do
      throwError m!"Unapproved axiom: {{dependency}}"
  logInfo "The endpoint uses only standard Lean axioms."
""",
        encoding="utf-8",
    )
    source.chmod(0o644)
    audit_log = logs / "axioms.log"
    with audit_log.open("wb") as output:
        result = subprocess.run(
            [lake, "--no-ansi", "env", "lean", str(source)],
            stdout=output,
            stderr=subprocess.STDOUT,
            check=False,
        )
    print(audit_log.read_text(encoding="utf-8"), end="")
    return result.returncode


def check_endpoint(lake, frequency, logs):
    module = f"Unfoldings.FewestNets.PaperFrequency{frequency}"
    log = logs / "endpoint.log"
    result = check_module(lake, module, log)
    print(f"{module} {'passed' if result == 0 else 'failed'}. See {log}")
    if result != 0:
        return result
    return audit_endpoint(lake, frequency, logs)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("frequency", type=int, choices=(100, 400))
    parser.add_argument("--workers", type=int, default=2)
    parser.add_argument("--lake", default="lake", help="Lake executable")
    args = parser.parse_args()
    if args.workers < 1:
        parser.error("--workers must be positive")

    root = Path(__file__).resolve().parent.parent
    os.chdir(root)
    frequency = args.frequency
    directory = Path(f"Unfoldings/FewestNets/Geometry{frequency}")
    blocks = sorted(directory.glob(f"Routing{frequency}Block*.lean"))
    if not blocks:
        parser.error(f"no routing certificate modules in {directory}")

    logs = Path(f".lake/routing-check/{frequency}")
    logs.mkdir(parents=True, exist_ok=True)
    failed = 0
    with ThreadPoolExecutor(max_workers=args.workers) as workers:
        pending = {
            workers.submit(check_module, args.lake, module_name(block),
                           logs / f"{block.stem}.log"): block
            for block in blocks
        }
        for job in as_completed(pending):
            block = pending[job]
            result = job.result()
            if result == 0:
                print(f"{block.stem} passed", flush=True)
            else:
                failed += 1
                print(f"{block.stem} failed ({result}). See {logs / (block.stem + '.log')}",
                      flush=True)

    if failed:
        print(f"{failed} of {len(blocks)} modules failed.")
        return 1

    return check_endpoint(args.lake, frequency, logs)


if __name__ == "__main__":
    raise SystemExit(main())
