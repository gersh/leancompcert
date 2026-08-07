import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk028

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360805061212144336, 360805061249295902⟩, ⟨(-699422106728711334), (-699422036031059208)⟩, true⟩

def state01 : KState := ⟨⟨361533647669053161, 361533647706484307⟩, ⟨(-2741813230001113262), (-2741813158519222196)⟩, true⟩

def words00 : List Nat := [360555572182755455, 360555849894952129, 360556253540912272, 360556656899073438, 360556922709590188, 360557153768238141, 360557376907392309, 360557599887680636, 360557913486339999, 360558260599220265]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 2800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 2800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨361499814286339283, 361499814324053618⟩, ⟨(-2646771736959745441), (-2646771664680646365)⟩, true⟩

def words01 : List Nat := [360558542256607796, 360558823713744598, 360559148837738696, 360559580962187437, 360559976360226075, 360560371477546987, 360560701214462691, 360560909866854560, 360561242811721688, 360561575520551085]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 2810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 2800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨361012428073496765, 361012428111492937⟩, ⟨(-1270934406111053134), (-1270934333035741826)⟩, true⟩

def words02 : List Nat := [360561841718590402, 360562080979097746, 360562255481809251, 360562429860982343, 360562567664799927, 360562774299899525, 360562991463420569, 360563208473420936, 360563334707562414, 360563493341787624]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 2820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 2800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨361786628418394704, 361786628456674067⟩, ⟨(-3466637945246818446), (-3466637871368673048)⟩, true⟩

def words03 : List Nat := [360563690839580253, 360563888197954869, 360564208620865861, 360564501865473880, 360564677264987191, 360564852540850841, 360565150637517899, 360565551362089265, 360565981318837114, 360566410972911775]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 2830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 2800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨361446034193409722, 361446034231976101⟩, ⟨(-2497082531713653375), (-2497082457018955723)⟩, true⟩

def words04 : List Nat := [360566776620215786, 360567178284966284, 360567702033429304, 360568225413712554, 360568712757531414, 360569081450612929, 360569370403828633, 360569659154202237, 360569864948777198, 360570172268798635]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 2840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 2800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨361007214175100872, 361007214213952049⟩, ⟨(-1242517214289230475), (-1242517138781407579)⟩, true⟩

def words05 : List Nat := [360570601195135645, 360571029820794026, 360571395421485237, 360571642947653290, 360571855133092960, 360572067170003899, 360572400383819021, 360572615704351170, 360572767661898950, 360572919513224539]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 2850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 2800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨361456249300214290, 361456249339352041⟩, ⟨(-2528963894791752918), (-2528963818462890652)⟩, true⟩

def words06 : List Nat := [360573192266213229, 360573533137772580, 360573865905734459, 360574198441402950, 360574427037626693, 360574538299940863, 360574704949228284, 360574871482352033, 360575077277137885, 360575384198821602]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 2860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 2800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360844329211764142, 360844329251192025⟩, ⟨(-770607656434109650), (-770607579271087190)⟩, true⟩

def words07 : List Nat := [360575589922512927, 360575795502995435, 360575982940218674, 360576230612160688, 360576415812375634, 360576600883850114, 360576690771888724, 360576690771919249, 360576757175021319, 360576850049778944]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 2870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 2800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨361299279878615569, 361299279918331385⟩, ⟨(-2084209306320454780), (-2084209228326735218)⟩, true⟩

def words08 : List Nat := [360576993566122114, 360577130088856704, 360577200156215611, 360577270175004805, 360577305868103531, 360577431500933791, 360577675776691638, 360577919883347884, 360578100254518798, 360578349711369526]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 2880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 2800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨361326150778362977, 361326150818368468⟩, ⟨(-2164347135010175454), (-2164347056177852666)⟩, true⟩

def words09 : List Nat := [360578575262569441, 360578800657848820, 360579036140409967, 360579156254293990, 360579175581655091, 360579194895675700, 360579332166615261, 360579566804452449, 360579824247240865, 360580081512550525]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 2890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 2800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 2800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk028
