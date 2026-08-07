import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk667

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360559793588468568, 360559822152176882⟩, ⟨1539964996835175146, 1541251951176603020⟩, true⟩

def state01 : KState := ⟨⟨360574156763067093, 360574185335672441⟩, ⟨581857650087065946, 583145197905032606⟩, true⟩

def words00 : List Nat := [360582929032162612, 360582928911070062, 360582928902491712, 360582928799775311, 360582928696982543, 360582928402566890, 360582927883683355, 360582927500482960, 360582927117007130, 360582926831668619]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 66700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 66700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360561987333660623, 360562015915222598⟩, ⟨1393759099357389889, 1395047244717301075⟩, true⟩

def words01 : List Nat := [360582926701472409, 360582926422784227, 360582926143923497, 360582926146877137, 360582926147670306, 360582926057905377, 360582925968059436, 360582925700742103, 360582925209023235, 360582924896708170]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 66710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 66700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360561260954251418, 360561289544682271⟩, ⟨1442228993000119022, 1443517730135080518⟩, true⟩

def words02 : List Nat := [360582924584090008, 360582924495830807, 360582924245545833, 360582923849934412, 360582923454168076, 360582922917401313, 360582922555112256, 360582922347788907, 360582922140372094, 360582921760029718]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 66720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 66700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360582449329855281, 360582477929179139⟩, ⟨28139915105229102, 29429245714487312⟩, true⟩

def words03 : List Nat := [360582921436633926, 360582921108675688, 360582920780450883, 360582920676499583, 360582920422014357, 360582919975931957, 360582919529687411, 360582919118344024, 360582918888447870, 360582918882815856]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 66730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 66700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360589201853115255, 360589230461409387⟩, ⟨(-422658847639514891), (-421368918311511381)⟩, true⟩

def words04 : List Nat := [360582918877047956, 360582918759315043, 360582918762324936, 360582918832577172, 360582918833379115, 360582918748798532, 360582918562800727, 360582918240030220, 360582917917081883, 360582917913008442]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 66740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 66700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360561492801528567, 360561521418702362⟩, ⟨1427148747604785862, 1428439269694608244⟩, true⟩

def words05 : List Nat := [360582918232311682, 360582918551802082, 360582918757883401, 360582918758825232, 360582918740883296, 360582918586333956, 360582918460295983, 360582918461238671, 360582918371991213, 360582918052460520]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 66750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 66700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360617301363100649, 360617329989165159⟩, ⟨(-2298920753064836074), (-2297629637386233190)⟩, true⟩

def words06 : List Nat := [360582917732726135, 360582917582921292, 360582917731369632, 360582917918093616, 360582917918962343, 360582917992378898, 360582918253039137, 360582918513972843, 360582918880839135, 360582919397180821]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 66760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 66700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360604697820540013, 360604726455589456⟩, ⟨(-1457330428592122946), (-1456038712946203854)⟩, true⟩

def words07 : List Nat := [360582919801604820, 360582920206110793, 360582920605617582, 360582921133576107, 360582921602493634, 360582922071552369, 360582922428517167, 360582922612502158, 360582922939766761, 360582923267363072]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 66770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 66700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360563894116803894, 360563922760718613⟩, ⟨1267688536688256929, 1268980844402281225⟩, true⟩

def words08 : List Nat := [360582923524047833, 360582923557103787, 360582923557943336, 360582923477887177, 360582923397681937, 360582923176546963, 360582923067618605, 360582922866210850, 360582922664714450, 360582922324192222]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 66780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 66700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360610241917275374, 360610270570087439⟩, ⟨(-1828131854053778567), (-1826838952042693777)⟩, true⟩

def words09 : List Nat := [360582922040491141, 360582921980774253, 360582921936434767, 360582922048794023, 360582922049663380, 360582921964941261, 360582922018028770, 360582922270439402, 360582922680607168, 360582923090977206]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 66790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 66700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 66700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk667
