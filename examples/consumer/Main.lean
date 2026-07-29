import Consumer

/-- Write the emitted C for the consumer's certified computation.
Usage: `consumer [output.c]` (default `demo.c`). -/
def main (args : List String) : IO UInt32 := do
  let file := args.headD "demo.c"
  match Consumer.emittedC with
  | .error errors =>
      for error in errors do
        IO.eprintln error
      pure 1
  | .ok source =>
      IO.FS.writeFile file source
      IO.println s!"wrote {file}"
      pure 0
