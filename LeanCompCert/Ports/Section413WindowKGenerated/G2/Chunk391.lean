import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk391

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360528914587517117, 360528923987054117⟩, ⟨2088710083617699985, 2088958494988994131⟩, true⟩

def state01 : KState := ⟨⟨360565049656825483, 360565059061359222⟩, ⟨675807525825607408, 676056132593644000⟩, true⟩

def words00 : List Nat := [360582348669586762, 360582347754106559, 360582347620782881, 360582347880625220, 360582347881120473, 360582347494466634, 360582346456779435, 360582346071579704, 360582345686252519, 360582345078556708]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 39100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 39100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360567913322912471, 360567922732480546⟩, ⟨563827441025279163, 564076244710970491⟩, true⟩

def words01 : List Nat := [360582344637054465, 360582343868982968, 360582343100849561, 360582343305386279, 360582343460900162, 360582343616505045, 360582343616979738, 360582343247504871, 360582342227383900, 360582341859390336]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 39110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 39100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360549530033461362, 360549539448019028⟩, ⟨1282899232861319892, 1283148231764013090⟩, true⟩

def words02 : List Nat := [360582341491241787, 360582341082429964, 360582340294463965, 360582338971642814, 360582337648803587, 360582336139412299, 360582334957027313, 360582333872801309, 360582332788572819, 360582331378296667]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 39120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 39100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360609647354468448, 360609656774016773⟩, ⟨(-1069830237191578985), (-1069581042979162949)⟩, true⟩

def words03 : List Nat := [360582330540720669, 360582330214208152, 360582330211893499, 360582330324728914, 360582330325216741, 360582329879186354, 360582329433084878, 360582329017016989, 360582329715650271, 360582330414368855]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 39130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 39100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360581988156671162, 360581997581263248⟩, ⟨12678821871696570, 12928213521355414⟩, true⟩

def words04 : List Nat := [360582330785337502, 360582330785866785, 360582330507113586, 360582330421187920, 360582330335116682, 360582330084198973, 360582329733877314, 360582329057722028, 360582328381502858, 360582327803830844]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 39140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 39100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360525711166343303, 360525720595927466⟩, ⟨2216109605728561722, 2216359192842900458⟩, true⟩

def words05 : List Nat := [360582327795833110, 360582327451219130, 360582327106565295, 360582326389096828, 360582325022253290, 360582323329594263, 360582321636864000, 360582320594936319, 360582319568609097, 360582318123834589]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 39150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 39100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360561360616954071, 360561370051531449⟩, ⟨820076350954036196, 820326133628327020⟩, true⟩

def words06 : List Nat := [360582316679010377, 360582315884921217, 360582315741149054, 360582315994812094, 360582315995308675, 360582315629305526, 360582314614235026, 360582314039969755, 360582313465574486, 360582312766201563]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 39160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 39100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360531191490458700, 360531200930083518⟩, ⟨2002012565399621785, 2002262545807657679⟩, true⟩

def words07 : List Nat := [360582312232028105, 360582311201531533, 360582310170977284, 360582309547462117, 360582309250281441, 360582308782884947, 360582308315459097, 360582307513376287, 360582306433596820, 360582305129823377]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 39170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 39100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360567054122545966, 360567063567160858⟩, ⟨596793504281702566, 597043680225629160⟩, true⟩

def words08 : List Nat := [360582303825941065, 360582303172138444, 360582302769417657, 360582301935782687, 360582301102104624, 360582299881482309, 360582299167802729, 360582298940204571, 360582298712560089, 360582298159664702]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 39180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 39100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360582395956352403, 360582405405976636⟩, ⟨(-4648617076317925), (-4398244791980945)⟩, true⟩

def words09 : List Nat := [360582298032259282, 360582298293723412, 360582298294162349, 360582298214989211, 360582297487828735, 360582296181662263, 360582294875461713, 360582293848538105, 360582293205295530, 360582293208716567]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 39190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 39100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 39100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk391
