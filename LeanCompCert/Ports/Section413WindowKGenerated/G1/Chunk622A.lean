import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk622A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362479857166932116, 362479914054172513⟩, ⟨339156528422051123, 341546549779405671⟩, true⟩

def state01 : KState := ⟨⟨362492612813578069, 362492669719750472⟩, ⟨(-454233769813000224), (-451842570791115160)⟩, true⟩

def words00 : List Nat := [371285405239841062, 371285405317745026, 371285405557956877, 371285405798996715, 371285405982411115, 371285405984526666, 371285406075948284, 371285406252854542, 371285406535266793, 371285406654202722]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 62200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 62200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362501923456551473, 362501980381930086⟩, ⟨(-1033492129492916674), (-1031099735556419434)⟩, true⟩

def words01 : List Nat := [371285406761679865, 371285406869847257, 371285407235797262, 371285407474013705, 371285407740823102, 371285408008505198, 371285408264082526, 371285408273950916, 371285408541730092, 371285408810667066]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 62210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 62200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362489857619638568, 362489914563842468⟩, ⟨(-282682837510088740), (-280289272165881188)⟩, true⟩

def words02 : List Nat := [371285409289178294, 371285409463744344, 371285409589449878, 371285409715864557, 371285409892246711, 371285409940303238, 371285410118787464, 371285410298097111, 371285410475611543, 371285410550213154]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 62220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 62200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362511711881268315, 362511768844572803⟩, ⟨(-1642775305900285017), (-1640380551830002265)⟩, true⟩

def words03 : List Nat := [371285410793403158, 371285411037691681, 371285411539332690, 371285411795700040, 371285412013585602, 371285412232085881, 371285412494084592, 371285412688616302, 371285413113509137, 371285413539358716]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 62230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 62200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362489225104788777, 362489282087149920⟩, ⟨(-243116846674038621), (-240720906424179181)⟩, true⟩

def words04 : List Nat := [371285413963287225, 371285414043644673, 371285414339332547, 371285414636167501, 371285414974686476, 371285414976798867, 371285414971356773, 371285414965599953, 371285415082224635, 371285415146756607]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 62240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 62200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk622A
