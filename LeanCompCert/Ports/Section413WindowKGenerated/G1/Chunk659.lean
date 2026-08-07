import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk659

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

def state06 : KState := ⟨⟨362501359669359672, 362501423937975855⟩, ⟨(-1052388199632805380), (-1049525033205452148)⟩, true⟩

def words05 : List Nat := [371285512051821964, 371285512009721588, 371285512120353384, 371285512122640711, 371285512089538597, 371285512020552774, 371285512108951552, 371285512154866089, 371285512397624760, 371285512641403556]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 65950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 65900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362489839090754523, 362489903379703220⟩, ⟨(-292453873703773925), (-289589366042678755)⟩, true⟩

def words06 : List Nat := [371285512833753969, 371285512850290053, 371285513095757352, 371285513342361516, 371285513643347501, 371285513645595507, 371285513640515727, 371285513590780662, 371285513664123790, 371285513733251860]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 65960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 65900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362476503763315017, 362476568072458270⟩, ⟨587391817920570596, 590257657923605400⟩, true⟩

def words07 : List Nat := [371285513980730076, 371285514229094212, 371285514476650055, 371285514478898243, 371285514420296941, 371285514348021425, 371285514345429050, 371285514347692492, 371285514214301784, 371285514081217343]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 65970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 65900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362477775825422303, 362477840154726374⟩, ⟨503576504755831853, 506443675070086677⟩, true⟩

def words08 : List Nat := [371285514041105739, 371285514054771165, 371285514296959195, 371285514540086860, 371285514751595179, 371285514753843778, 371285514664397378, 371285514672342877, 371285514704225763, 371285514706553471]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 65980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 65900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362483001739416482, 362483066089226937⟩, ⟨158725218012671002, 161593741643749154⟩, true⟩

def words09 : List Nat := [371285514591937696, 371285514478063414, 371285514476386964, 371285514498577799, 371285514578229890, 371285514658762296, 371285514738037237, 371285514740286311, 371285514513509939, 371285514479251843]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 65990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 65900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 65900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk659
