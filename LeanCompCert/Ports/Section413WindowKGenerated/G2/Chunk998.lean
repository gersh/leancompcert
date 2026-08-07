import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk998

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360584465534823415, 360584531530730529⟩, ⟨(-213668528777273346), (-209221249785728006)⟩, true⟩

def state01 : KState := ⟨⟨360576793514411182, 360576859524151079⟩, ⟨551917303265649266, 556365962838017046⟩, true⟩

def words00 : List Nat := [360582435147739361, 360582435105699527, 360582434984449735, 360582434848621245, 360582434712410432, 360582434551049314, 360582434391714277, 360582434152663814, 360582433913339791, 360582433774855799]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 99800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 99800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360577002536561193, 360577068559992077⟩, ⟨531088129017645950, 535538155155140126⟩, true⟩

def words01 : List Nat := [360582433746581314, 360582433774432704, 360582433775749046, 360582433718370581, 360582433695802340, 360582433648220554, 360582433651352569, 360582433652805715, 360582433650828169, 360582433598613147]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 99810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 99800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360602183973411150, 360602250010543388⟩, ⟨(-1982634540698770606), (-1978183146826962188)⟩, true⟩

def words02 : List Nat := [360582433574686890, 360582433663418905, 360582433852029597, 360582434040918927, 360582434130929749, 360582434226393558, 360582434281097697, 360582434336216933, 360582434491191343, 360582434691185404]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 99820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 99800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360604736307709757, 360604802358662742⟩, ⟨(-2237442509209058446), (-2232989735540840006)⟩, true⟩

def words03 : List Nat := [360582434835812088, 360582434980594483, 360582435225389675, 360582435548243741, 360582435823531610, 360582436099060452, 360582436324173375, 360582436449359767, 360582436674550908, 360582436900228424]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 99830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 99800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360580600641900625, 360580666706546216⟩, ⟨172327596049042617, 176781736854576977⟩, true⟩

def words04 : List Nat := [360582437082283054, 360582437164524214, 360582437182026618, 360582437199685601, 360582437200903395, 360582437200596533, 360582437210947339, 360582437221592798, 360582437222886625, 360582437179624380]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 99840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 99800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360596548656746827, 360596614735096118⟩, ⟨(-1420224495686082347), (-1415768986498868703)⟩, true⟩

def words05 : List Nat := [360582437205870279, 360582437250272673, 360582437324111704, 360582437325564123, 360582437299553206, 360582437179111434, 360582437058393657, 360582437052024157, 360582437195173670, 360582437338650070]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 99850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 99800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595406675224605, 360595472767423692⟩, ⟨(-1306203133575707425), (-1301746241279311019)⟩, true⟩

def words06 : List Nat := [360582437431641800, 360582437529062892, 360582437684714198, 360582437840807263, 360582437971101590, 360582438118672367, 360582438215815241, 360582438313114890, 360582438358624415, 360582438490794047]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 99860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 99800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360577133214384542, 360577199320263444⟩, ⟨518911408498159261, 523369667063582425⟩, true⟩

def words07 : List Nat := [360582438722700564, 360582438954881060, 360582439132561024, 360582439210370651, 360582439221166720, 360582439232372870, 360582439343334530, 360582439354564649, 360582439355864875, 360582439304915663]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 99870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 99800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360585271777822518, 360585337897417527⟩, ⟨(-294000554558239588), (-289540925959297660)⟩, true⟩

def words08 : List Nat := [360582439301372823, 360582439407347495, 360582439479672746, 360582439552252040, 360582439553591683, 360582439541051811, 360582439428237902, 360582439384193879, 360582439339726174, 360582439328718052]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 99880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 99800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360579737106737746, 360579803240178417⟩, ⟨258883091682179594, 263344103389695322⟩, true⟩

def words09 : List Nat := [360582439330033263, 360582439283724250, 360582439271914411, 360582439358373562, 360582439419066979, 360582439479996446, 360582439481313730, 360582439452607613, 360582439341999236, 360582439317289425]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 99890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 99800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 99800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk998
