import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk869

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360585152505848762, 360585202009334097⟩, ⟨(-265218429443054363), (-262313352758273647)⟩, true⟩

def state01 : KState := ⟨⟨360569306704915156, 360569356220296547⟩, ⟨1111741172330447420, 1114647282841360970⟩, true⟩

def words00 : List Nat := [360582183479559406, 360582183441617415, 360582183271110846, 360582183153934387, 360582183036435584, 360582182805615554, 360582182517533206, 360582182150500084, 360582181783235735, 360582181525587554]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 86900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 86900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360541515561083393, 360541565088256144⟩, ⟨3527220319874597680, 3530127455232182172⟩, true⟩

def words01 : List Nat := [360582181379037039, 360582181253310661, 360582181127441973, 360582180903771843, 360582180547608770, 360582180158470328, 360582179768974990, 360582179442355672, 360582179077632606, 360582178611671149]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 86910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 86900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360582245208100815, 360582294747076536⟩, ⟨(-13224348510329692), (-10316187180256070)⟩, true⟩

def words02 : List Nat := [360582178145438495, 360582177724594092, 360582177404859407, 360582177217550394, 360582177030151566, 360582176729279905, 360582176433303682, 360582176269870117, 360582176106072969, 360582176076094030]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 86920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 86900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360573914004311930, 360573963555229269⟩, ⟨710989918898154357, 713899118370057617⟩, true⟩

def words03 : List Nat := [360582176077224116, 360582175996281569, 360582175915125735, 360582175766930423, 360582175685053208, 360582175570081910, 360582175454976752, 360582175273817615, 360582175048237729, 360582174955256530]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 86930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 86900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360575220683709637, 360575270246401865⟩, ⟨597369567241747572, 600279790481273460⟩, true⟩

def words04 : List Nat := [360582174873765233, 360582174875017287, 360582174817367282, 360582174686731765, 360582174555877965, 360582174392082297, 360582174308421466, 360582174221593973, 360582174134642391, 360582173981772553]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 86940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 86900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360604729793100316, 360604779367599144⟩, ⟨(-1968602412772940309), (-1965691162890298179)⟩, true⟩

def words05 : List Nat := [360582173956085899, 360582174010163509, 360582174164394964, 360582174322522773, 360582174345874610, 360582174369311405, 360582174431886922, 360582174561155859, 360582174822112207, 360582175083346545]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 86950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 86900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360598426073040101, 360598475659473747⟩, ⟨(-1420566170037948415), (-1417653882244928261)⟩, true⟩

def words06 : List Nat := [360582175224476416, 360582175233593277, 360582175239915599, 360582175246601693, 360582175247649074, 360582175223496692, 360582175224623177, 360582175161234988, 360582175164969727, 360582175353828821]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 86960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 86900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360564175671562749, 360564225269772291⟩, ⟨1558410888219963105, 1561324200221937501⟩, true⟩

def words07 : List Nat := [360582175614471372, 360582175875350386, 360582176058205328, 360582176109094559, 360582176110162025, 360582176062321091, 360582176014107596, 360582175986651892, 360582175856551944, 360582175651471785]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 86970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 86900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360581584604621043, 360581634214667980⟩, ⟨44171633882871147, 47085975558062691⟩, true⟩

def words08 : List Nat := [360582175446112303, 360582175403295334, 360582175473831646, 360582175544601675, 360582175545766990, 360582175503533961, 360582175496783509, 360582175532766137, 360582175533798901, 360582175494993973]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 86980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 86900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360571399746986856, 360571449368952704⟩, ⟨930247570243377800, 933162948801425212⟩, true⟩

def words09 : List Nat := [360582175489887022, 360582175412016527, 360582175386759240, 360582175509412231, 360582175578119833, 360582175647058020, 360582175648173717, 360582175641072218, 360582175501716029, 360582175379858468]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 86990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 86900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 86900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk869
