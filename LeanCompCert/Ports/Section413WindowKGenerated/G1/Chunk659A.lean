import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk659A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362499592301824450, 362499656449016595⟩, ⟨(-934877817718727676), (-932022656788699714)⟩, true⟩

def state01 : KState := ⟨⟨362481141673699610, 362481205841136509⟩, ⟨281061338442797257, 283917833606526087⟩, true⟩

def words00 : List Nat := [371285513849958024, 371285513852204022, 371285513830796490, 371285513917454767, 371285514010740950, 371285514012988533, 371285513847179073, 371285513683242195, 371285513518421320, 371285513500575237]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 65900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 65900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362467984878081025, 362468049065792291⟩, ⟨1148351789937569787, 1151209621485710617⟩, true⟩

def words01 : List Nat := [371285513539213842, 371285513644195009, 371285513740512442, 371285513742758461, 371285513532320482, 371285513393437119, 371285513282355049, 371285513284604412, 371285513066353044, 371285512803982305]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 65910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 65900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362491501747143027, 362491565954948700⟩, ⟨(-401996735073208901), (-399137578798185205)⟩, true⟩

def words02 : List Nat := [371285512540586895, 371285512508119558, 371285512359750757, 371285512280718538, 371285512201028412, 371285512090816406, 371285511836422668, 371285511813161522, 371285511992678893, 371285512086832061]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 65920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 65900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362491266759884923, 362491330988173658⟩, ⟨(-386492603951848254), (-383632097126929708)⟩, true⟩

def words03 : List Nat := [371285512180253272, 371285512274410252, 371285512463405767, 371285512574431138, 371285512754956061, 371285512936377032, 371285513120663004, 371285513122909873, 371285513088839121, 371285513179873406]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 65930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 65900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362467337771284418, 362467402019564025⟩, ⟨1191512811770095795, 1194374636898750691⟩, true⟩

def words04 : List Nat := [371285513383221509, 371285513385468676, 371285513282595221, 371285513151665395, 371285513019869919, 371285512899134425, 371285512686077184, 371285512569622773, 371285512452445569, 371285512324899867]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 65940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 65900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk659A
