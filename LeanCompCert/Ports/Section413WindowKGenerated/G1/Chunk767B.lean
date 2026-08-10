import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk767A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk767B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk767A

def state06 : KState := ⟨⟨362488027721973164, 362488115793992485⟩, ⟨(-228143982525329782), (-223578719748238166)⟩, true⟩

def words05 : List Nat := [371285203866249821, 371285203774851301, 371285203756937960, 371285203759583208, 371285203610475552, 371285203402012420, 371285203192499761, 371285203153697579, 371285203092712176, 371285203133660439]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 76750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 76700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362471562176269847, 362471650272195899⟩, ⟨1035846439133911323, 1040413537116663421⟩, true⟩

def words06 : List Nat := [371285203175491099, 371285203178182923, 371285203102792180, 371285203130066058, 371285203187632757, 371285203190278766, 371285203042139764, 371285202895031856, 371285202746857253, 371285202617345263]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 76760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 76700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362472163958753992, 362472252078487090⟩, ⟨989691196967927362, 994260122739635678⟩, true⟩

def words07 : List Nat := [371285202442610303, 371285202438446125, 371285202433404562, 371285202416450560, 371285202216272551, 371285202046900727, 371285201876082411, 371285201875622191, 371285201711783312, 371285201546092452]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 76770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 76700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362479069922861832, 362479158066289146⟩, ⟨459450546323831023, 464021291459426275⟩, true⟩

def words08 : List Nat := [371285201380061234, 371285201382977787, 371285201311378945, 371285201310403849, 371285201308569630, 371285201280146409, 371285201024916680, 371285200913678926, 371285200801072718, 371285200797002253]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 76780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 76700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362482567256911424, 362482655424468645⟩, ⟨190867722636243320, 195440320822405124⟩, true⟩

def words09 : List Nat := [371285200720312913, 371285200617632772, 371285200537497078, 371285200540413677, 371285200481135993, 371285200474675510, 371285200467401581, 371285200425298183, 371285200250124504, 371285200220312687]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 76790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 76700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 76700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk767B
