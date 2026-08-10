import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk403A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360533216343394904, 360533226353237426⟩, ⟨1993151991790467795, 1993424634226333099⟩, true⟩

def state01 : KState := ⟨⟨360598842093527733, 360598852108523693⟩, ⟨(-651906828685132725), (-651633978539684339)⟩, true⟩

def words00 : List Nat := [360582689757421731, 360582689007946766, 360582688571176446, 360582688491359471, 360582688411500275, 360582687807199197, 360582687217250440, 360582686832249450, 360582686541633192, 360582686943220434]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 40300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 40300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360558591160043089, 360558601180254935⟩, ⟨970764984088090059, 971038044512182513⟩, true⟩

def words01 : List Nat := [360582687033357876, 360582687123545530, 360582687123997218, 360582687096180705, 360582687096641228, 360582686832815140, 360582686568942618, 360582685946488958, 360582685061768012, 360582684465089067]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 40310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 40300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360551887167665881, 360551897193023391⟩, ⟨1241044894982539231, 1241318162905372245⟩, true⟩

def words02 : List Nat := [360582683868242361, 360582683703073751, 360582682925616746, 360582681840461262, 360582680755269632, 360582679514113326, 360582678790830083, 360582678037112819, 360582677283377714, 360582676220122459]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 40320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 40300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360575645388771429, 360575655419288975⟩, ⟨282843970053690194, 283117446106109180⟩, true⟩

def words03 : List Nat := [360582675457404403, 360582675062009290, 360582674689199270, 360582674946258900, 360582674946763033, 360582674680699309, 360582674414548091, 360582673981652720, 360582673873471575, 360582673700055116]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 40330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 40300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360564340942009456, 360564350977740992⟩, ⟨738718720657413347, 738992407067819459⟩, true⟩

def words04 : List Nat := [360582673526578257, 360582672815554155, 360582671829995746, 360582671457772582, 360582671085423009, 360582670556603571, 360582669416181478, 360582667966803256, 360582666517379125, 360582665535536973]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 40340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 40300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk403A
