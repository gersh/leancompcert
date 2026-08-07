import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk657

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360563807247063981, 360563834927386806⟩, ⟨1251491190272706429, 1252719663353707437⟩, true⟩

def state01 : KState := ⟨⟨360583443682680376, 360583471371736530⟩, ⟨(-38665422855416112), (-37436375951241886)⟩, true⟩

def words00 : List Nat := [360582901908293463, 360582901930462253, 360582901931292929, 360582901839003044, 360582901746566781, 360582901516654954, 360582901560575881, 360582901698721867, 360582901699569423, 360582901659269040]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 65700 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 65700 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360635015812124277, 360635043509922565⟩, ⟨(-3427779436841196194), (-3426549815448194624)⟩, true⟩

def words01 : List Nat := [360582901778385436, 360582901897769259, 360582902248108658, 360582902664070796, 360582902877686141, 360582903091379154, 360582903536078394, 360582904099284241, 360582904893390013, 360582905687682365]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 65710 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 65700 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360616084287333138, 360616111993966444⟩, ⟨(-2183672541776547501), (-2182442339703095941)⟩, true⟩

def words02 : List Nat := [360582906342201601, 360582906920552261, 360582907418816485, 360582907917323817, 360582908259217664, 360582908453620460, 360582908509925383, 360582908566326225, 360582908853690344, 360582909359901801]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 65720 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 65700 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360586844645042983, 360586872360395325⟩, ⟨(-261477614175096889), (-260246838954987633)⟩, true⟩

def words03 : List Nat := [360582910096911925, 360582910834077005, 360582911455294885, 360582911973096974, 360582912432645752, 360582912892442476, 360582913346251985, 360582913569471309, 360582913630517943, 360582913691696112]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 65730 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 65700 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360593766918898515, 360593794642992678⟩, ⟨(-716570595640512191), (-715339245689097933)⟩, true⟩

def words04 : List Nat := [360582913812173142, 360582914048642299, 360582914409350189, 360582914770239965, 360582914934725505, 360582914936586960, 360582914937341564, 360582914899578878, 360582914957687285, 360582915124115565]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 65740 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 65700 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360603650672229308, 360603678405166048⟩, ⟨(-1366530971292898675), (-1365299039899538655)⟩, true⟩

def words05 : List Nat := [360582915124956298, 360582915106243583, 360582915222084889, 360582915503678812, 360582915727006222, 360582915950480460, 360582916024427681, 360582916240917810, 360582916557395217, 360582916874168960]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 65750 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 65700 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360595250251995711, 360595277993651701⟩, ⟨(-814056989499743371), (-812824484683547873)⟩, true⟩

def words06 : List Nat := [360582917421522992, 360582917797339618, 360582918056775400, 360582918316297036, 360582918416938287, 360582918656435292, 360582918964126793, 360582919271982826, 360582919402382245, 360582919591245116]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 65760 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 65700 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360602436854348876, 360602464604775813⟩, ⟨(-1286783898716939850), (-1285550816995440078)⟩, true⟩

def words07 : List Nat := [360582919954124338, 360582920317293681, 360582920673247233, 360582920798902498, 360582920799758492, 360582920728446785, 360582920815520458, 360582921119300040, 360582921417166535, 360582921715233310]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 65770 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 65700 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360617882896289432, 360617910655543397⟩, ⟨(-2303061402810249325), (-2301827740404142527)⟩, true⟩

def words08 : List Nat := [360582921897018023, 360582921941547197, 360582922166294396, 360582922391306654, 360582922502722034, 360582922694378390, 360582922770250780, 360582922846221992, 360582923152718685, 360582923685586958]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 65780 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 65700 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360580547604411517, 360580575372410125⟩, ⟨153440058917683877, 154674296677949349⟩, true⟩

def words09 : List Nat := [360582924253917899, 360582924822404037, 360582925201062526, 360582925418970105, 360582925578793931, 360582925738858554, 360582925998863146, 360582926079524014, 360582926080358861, 360582926045611918]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 65790 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 65700 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 65700 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk657
