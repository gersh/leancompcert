import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk527A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360587462492508975, 360587479990356003⟩, ⟨(-288431403600235360), (-287808339721227134)⟩, true⟩

def state01 : KState := ⟨⟨360582116552841317, 360582134057654094⟩, ⟨(-6891666901946452), (-6268235893765830)⟩, true⟩

def words00 : List Nat := [360582018835820058, 360582018667233990, 360582018396072746, 360582018115617975, 360582017834972202, 360582017411917927, 360582016888685289, 360582016185491583, 360582015482184745, 360582015140617921]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 52700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 52700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360532832379419486, 360532849891107095⟩, ⟨2591249868264615351, 2591873661680397899⟩, true⟩

def words01 : List Nat := [360582015502651556, 360582015864816260, 360582016046688013, 360582016047418590, 360582015870196466, 360582015491809852, 360582015113234143, 360582014580541743, 360582013828621283, 360582012896829410]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 52710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 52700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360576459590594068, 360576477109178614⟩, ⟨291020102723394023, 291644259779111155⟩, true⟩

def words02 : List Nat := [360582011964907448, 360582011392319244, 360582011062987453, 360582010788093491, 360582010513142709, 360582009910845986, 360582009102529475, 360582008653457076, 360582008204183781, 360582008007334865]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 52720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 52700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360590806904355617, 360590824429914835⟩, ⟨(-465606011801583351), (-464981486937863617)⟩, true⟩

def words03 : List Nat := [360582007903115558, 360582007525375355, 360582007147509581, 360582007439577083, 360582007610955049, 360582007782445687, 360582007783096783, 360582007775019770, 360582007942783627, 360582008110790476]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 52730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 52700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360577479919600531, 360577497452037707⟩, ⟨237231612772645307, 237856500415006801⟩, true⟩

def words04 : List Nat := [360582008385517679, 360582008386248658, 360582008302449344, 360582008038974621, 360582007775403955, 360582007171756888, 360582006799676739, 360582006786443665, 360582006773137318, 360582006580007660]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 52740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 52700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk527A
