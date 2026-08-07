import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk077

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362602340779671621, 362602341507611859⟩, ⟨(-908381699398834367), (-908377903762379113)⟩, true⟩

def state01 : KState := ⟨⟨362399149982251297, 362399150712173977⟩, ⟨656934643225246290, 656938454136758858⟩, true⟩

def words00 : List Nat := [371284398453913707, 371284398454133688, 371284396024747926, 371284403218511577, 371284411833085856, 371284411833305931, 371284398058590212, 371284380771853220, 371284363489515075, 371284356737353842]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 7700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 7700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362438747404927808, 362438748136836409⟩, ⟨351748938488655775, 351752764721906339⟩, true⟩

def words01 : List Nat := [371284345687572934, 371284343135302645, 371284340583619210, 371284337951123323, 371284326569414769, 371284320175827679, 371284324142005999, 371284324142227196, 371284317869029571, 371284311966463599]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 7710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 7700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362540748603084084, 362540749336972991⟩, ⟨(-435908382888903640), (-435904541357825872)⟩, true⟩

def words02 : List Nat := [371284307169411697, 371284307169659583, 371284317607171244, 371284331187544041, 371284341800474208, 371284341800694992, 371284335195514194, 371284340249950723, 371284358063606408, 371284365358010655]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 7720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 7700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362458775755315863, 362458776491215349⟩, ⟨198137796961075951, 198141654044222143⟩, true⟩

def words03 : List Nat := [371284372600965911, 371284379842118223, 371284390745171007, 371284393400365524, 371284394505942945, 371284395611316446, 371284396614538775, 371284396614760041, 371284379495729212, 371284376188120288]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 7730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 7700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362446530958932489, 362446531696807294⟩, ⟨293531583889521626, 293535456271723902⟩, true⟩

def words04 : List Nat := [371284386228829595, 371284386817527475, 371284386817693463, 371284385962128301, 371284389221234487, 371284389221478012, 371284394044478877, 371284402974902365, 371284407239322541, 371284407239552033]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 7740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 7700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362645101048781472, 362645101788661355⟩, ⟨(-1246526678072390960), (-1246522790140792290)⟩, true⟩

def words05 : List Nat := [371284408680620361, 371284415006708757, 371284437930951183, 371284438743469673, 371284438743642628, 371284434493631027, 371284442578374738, 371284446705111682, 371284467408237357, 371284488106128075]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 7750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 7700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362509611231704154, 362509611973587072⟩, ⟨(-194903631251607985), (-194899727765976165)⟩, true⟩

def words06 : List Nat := [371284509319709969, 371284509319931736, 371284514591690054, 371284520720452806, 371284531827432727, 371284531827656069, 371284528383814812, 371284524943469573, 371284528353282903, 371284531581389675]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 7760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 7700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362369067900780591, 362369068644663493⟩, ⟨898588107586572378, 898592026622256758⟩, true⟩

def words07 : List Nat := [371284546534248875, 371284561483347983, 371284576319127304, 371284578136056846, 371284584715678662, 371284591293722403, 371284598506811623, 371284598507034016, 371284583752607938, 371284568905154786]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 7770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 7700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362515170326494208, 362515171072369724⟩, ⟨(-238663567395845148), (-238659632847421736)⟩, true⟩

def words08 : List Nat := [371284554061422559, 371284552414284340, 371284545940174664, 371284549274352729, 371284549904238508, 371284549904461706, 371284534104870126, 371284528727130144, 371284534405534383, 371284538338080491]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 7780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 7700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362546890186135577, 362546890934046716⟩, ⟨(-485751025485334524), (-485747075069171036)⟩, true⟩

def words09 : List Nat := [371284539201683694, 371284540065139628, 371284557343589581, 371284566491575438, 371284580594806548, 371284594694502515, 371284607976018471, 371284607976245269, 371284615667733614, 371284623650997214]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 7790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 7700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 7700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk077
