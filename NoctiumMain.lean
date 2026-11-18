import Noctium.Cli
import Noctium.Compiler
import Noctium.Frontend

def main (args : List String) : IO UInt32 := Noctium.Cli.run args
