import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk190

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360378316557496144, 360378318643263454⟩, ⟨3928551008876192379, 3928577831215354357⟩, true⟩

def state01 : KState := ⟨⟨360559005571864576, 360559007659921290⟩, ⟨494537707972353660, 494564573821762814⟩, true⟩

def words00 : List Nat := [360585075015819863, 360585066889604238, 360585060176135546, 360585055051519068, 360585049927426593, 360585042241620992, 360585035462580053, 360585030617960992, 360585025773776570, 360585023681689926]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 19000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 19000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360499255762066012, 360499257852435624⟩, ⟨1631024274443634792, 1631051184272921468⟩, true⟩

def words01 : List Nat := [360585022313434073, 360585019565922822, 360585016821918551, 360585018233900286, 360585018949119128, 360585019664302362, 360585019664520549, 360585018980810146, 360585016892291259, 360585012383680258]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 19010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 19000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360503892085003889, 360503894177660770⟩, ⟨1542496305149367944, 1542523258494087796⟩, true⟩

def words02 : List Nat := [360585007875463695, 360585004599976128, 360584998571418684, 360584990561486341, 360584982552356391, 360584973803129809, 360584967259020398, 360584962506772186, 360584957754996818, 360584951626872231]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 19020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 19000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360602568102514990, 360602570197467875⟩, ⟨(-335972595782857354), (-335945598733788734)⟩, true⟩

def words03 : List Nat := [360584947367836635, 360584945853837684, 360584944339929090, 360584942758164521, 360584939686069435, 360584934225824637, 360584928766107099, 360584926049858159, 360584925995597314, 360584926922496299]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 19030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 19000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360520716566188392, 360520718663455435⟩, ⟨1222404719575760034, 1222431760697896560⟩, true⟩

def words04 : List Nat := [360584926922714244, 360584925706431970, 360584921741752651, 360584919739576021, 360584917737543772, 360584914216530378, 360584908933460834, 360584901496626301, 360584894060526230, 360584888309686296]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 19040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 19000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360459077293178666, 360459079392736898⟩, ⟨2397260328536602938, 2397287413317521214⟩, true⟩

def words05 : List Nat := [360584884941574656, 360584884312707544, 360584883683880400, 360584881303173775, 360584879040316041, 360584875291224782, 360584871542457066, 360584867053325709, 360584861826679768, 360584855227643379]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 19050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 19000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360482170620888117, 360482172722746722⟩, ⟨1956800608618427328, 1956827737256020008⟩, true⟩

def words06 : List Nat := [360584848629247968, 360584841869944439, 360584836556897883, 360584831660028306, 360584826763653563, 360584819436824709, 360584809370183203, 360584800537657373, 360584791705982496, 360584785608811537]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 19060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 19000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360483551183269386, 360483553287449161⟩, ⟨1930477016480180575, 1930504189393742305⟩, true⟩

def words07 : List Nat := [360584780228459656, 360584772999127166, 360584765770506276, 360584761275381437, 360584759249298686, 360584755318570609, 360584751388227511, 360584746090055287, 360584738055207033, 360584732752302083]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 19070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 19000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360561178044829878, 360561180151307397⟩, ⟨449079969211848332, 449107185977798240⟩, true⟩

def words08 : List Nat := [360584727449870250, 360584724878778805, 360584723442831426, 360584720640086271, 360584717837595382, 360584713147981194, 360584709855421655, 360584709292561914, 360584708729740351, 360584705933705396]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 19080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 19000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360588036772501706, 360588038881281500⟩, ⟨(-63939424534138624), (-63912163806532158)⟩, true⟩

def words09 : List Nat := [360584704701606198, 360584704381894873, 360584705554889289, 360584705555133183, 360584704314272239, 360584700730240994, 360584697146533588, 360584694143341975, 360584692694442080, 360584692869878614]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 19090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 19000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 19000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk190
