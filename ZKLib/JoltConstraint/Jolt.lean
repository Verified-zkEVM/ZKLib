import ZKLib.JoltConstraint.Constants
import ZKLib.JoltConstraint.Field
import ZKLib.JoltConstraint.Trace
import ZKLib.JoltConstraint.Bytecode
import ZKLib.JoltConstraint.R1CS
import ZKLib.JoltConstraint.InstructionLookup
import ZKLib.JoltConstraint.ReadWriteMemory

/-!
  # The Jolt Relation

  This file contains the specification for the Jolt relation, which is a combination of R1CS,
  lookups, and memory-checking (both read-only and read-write).

  We will show that the Jolt relation is exactly equal to the execution of RISC-V programs.

  Many of our specification draws directly from the main [Rust codebase](https://github.com/a16z/jolt).

  TODO: establish a workflow for updating the spec & proof here when the Rust code changes.
  Maybe let's first build the architecture here to be able to state the desired theorem
  (i.e. Jolt's constraint system correctly constrains execution of RISC-V programs).
  Then we leave this theorem unproved until we have a relatively stable Rust version.
-/


namespace Jolt

variable (F : Type) [JoltField F]

-- TODO: will need to add R1CS constraints as part of `JoltPreprocessing`.
-- Right now, we "hard-code" the R1CS constraints as a bunch of conditions on the R1CS witness
/-- The full Jolt preprocessing, containing all the preprocessing components -/
structure Preprocessing extends
  Bytecode.Preprocessing F,
  ReadWriteMemory.Preprocessing,
  InstructionLookup.Preprocessing F
deriving Repr, Inhabited

-- Define abbreviations for the preprocessing fields

abbrev Preprocessing.toBytecode (preprocessing : Preprocessing F) : Bytecode.Preprocessing F :=
  preprocessing.toPreprocessing

abbrev Preprocessing.toReadWriteMemory (preprocessing : Preprocessing F) : ReadWriteMemory.Preprocessing :=
  preprocessing.toPreprocessing_1

abbrev Preprocessing.toInstructionLookup (preprocessing : Preprocessing F) : InstructionLookup.Preprocessing F :=
  preprocessing.toPreprocessing_2


def Preprocessing.new (bytecode : Array Bytecode.Row) (memoryInit : Array (UInt64 × UInt8)) (instructionSet : InstructionSet F) (subtableSet : SubtableSet F logM) : Preprocessing F :=
  let bytecodePrep := Bytecode.Preprocessing.new F bytecode
  let memoryPrep := ReadWriteMemory.Preprocessing.new memoryInit
  let instructionLookupsPrep := InstructionLookup.Preprocessing.new F instructionSet subtableSet
  Preprocessing.mk bytecodePrep memoryPrep instructionLookupsPrep

/-- The full Jolt witness, containing all the witness components -/
structure Witness (C logM : Nat) extends Bytecode.Witness F, ReadWriteMemory.Witness F,
    ReadWriteMemory.WitnessRangeCheck F, InstructionLookup.Witness F C logM, R1CS.WitnessAux F

-- Define abbreviations for the witness fields

abbrev Witness.toBytecode (witness : Witness F C logM) : Bytecode.Witness F :=
  witness.toWitness

abbrev Witness.toReadWriteMemory (witness : Witness F C logM) : ReadWriteMemory.Witness F :=
  witness.toWitness_1

abbrev Witness.toInstructionLookup (witness : Witness F C logM) : InstructionLookup.Witness F C logM :=
  witness.toWitness_2

abbrev Witness.toRangeCheck (witness : Witness F C logM) : ReadWriteMemory.WitnessRangeCheck F :=
  witness.toWitnessRangeCheck

abbrev Witness.toR1CSAux (witness : Witness F C logM) : R1CS.WitnessAux F :=
  witness.toWitnessAux


-- Generate witness from `Array ELFInstruction` and `Array (UInt64 × UInt8)`


-- TODO: this depends on the `InstructionSet` and `SubtableSet`
def InstructionLookupsWitness.new
    (preprocessedInstructionLookups : InstructionLookup.Preprocessing F)
    (trace : Array (TraceStep C logM)) : InstructionLookup.Witness F C logM := sorry

def InstructionLookupsWitness.getFlags (w : InstructionLookup.Witness F C logM) : Array F := sorry

-- Also supposed to return `readTimestamp`
def ReadWriteMemoryWitness.new (programIo : Device)
    (loadStoreFlags : Array F)
    (preprocessedRWMemory : ReadWriteMemory.Preprocessing)
    (trace : Array (TraceStep C logM)) : ReadWriteMemory.Witness F := sorry

def ReadWriteMemoryWitness.getReadTimestamps (w : ReadWriteMemory.Witness F) : Array F := sorry

def BytecodeWitness.new (preprocessedBytecode : Bytecode.Preprocessing F)
    (trace : Array (TraceStep C logM)) : Bytecode.Witness F := sorry

def RangeCheckWitness.new (readTimestamps : Array F) : ReadWriteMemory.WitnessRangeCheck F := sorry


-- Combine the witness generation from the previous functions
def Witness.new (programIo : Device)
    (preprocessing : Preprocessing F)
    (trace : Array (TraceStep C logM)) : Witness F C logM := sorry
  -- let instructionLookupsWitness := InstructionLookup.Witness.new F preprocessing.toInstructionLookup.Preprocessing trace
  -- let loadStoreFlags := instructionLookupsWitness.getFlags
  -- let bytecodeWitness := Bytecode.Witness.new F preprocessing.toBytecodePreprocessing trace
  -- let rwMemoryWitness := ReadWriteMemory.Witness.new F programIo loadStoreFlags preprocessing.toReadWriteMemoryPreprocessing trace
  -- let rangeCheckWitness := ReadWriteMemory.WitnessRangeCheck.new F rwMemoryWitness.getReadTimestamps
  -- { toBytecodeWitness := bytecodeWitness,
  --   toReadWriteMemoryWitness := rwMemoryWitness,
  --   toRangeCheckWitness := rangeCheckWitness,
  --   toInstructionLookupsWitness := instructionLookupsWitness }

/-- Define the conversion of the Jolt witness to the R1CS witness (both main and auxiliary parts),
  that is then used in the R1CS constraints -/
def Witness.toR1CS (wit : Witness F C logM) : R1CS.Witness F := sorry


def Witness.isValid (preprocess : Preprocessing F) (wit : Witness F C logM) : Prop :=
  Bytecode.isValid F (preprocess.toBytecode F) (wit.toBytecode F) ∧
  ReadWriteMemory.isValid F (preprocess.toReadWriteMemory F) (wit.toReadWriteMemory F) ∧
  ReadWriteMemory.WitnessRangeCheck.isValid F (wit.toRangeCheck F) ∧
  InstructionLookup.isValid F (preprocess.toInstructionLookup F) (wit.toInstructionLookup F) ∧
  R1CS.isValid F (wit.toR1CS F)


/-
  ## Theorem statement that Jolt proves correct execution of RISC-V programs

  This is an `if and only if` statement.

  Jolt Preprocessing is deterministically obtained from an `ELF` file,
  which contains a list of RISC-V instructions.

  Jolt Relation is satisfied (i.e. the Jolt verifier accepts), with respect to an `ELF` file and
  a public input-ouput pair of the program...

  `if and only if` there exists a unique Jolt witness that corresponds to an execution trace
  of the same program, producing the same input-output pair.
-/



end Jolt
