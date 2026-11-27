import PureSFormal.Cook.CTS
open PureSFormal.Cook

-- A mathematical table transcription. No runtime result enters a Lean proof.
def main : IO Unit :=
  for symbol in alphabet do
    IO.println (toString ((production symbol).map symbolIndex))
