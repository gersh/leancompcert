import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk371A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360587501301597833, 360587509727942470⟩, ⟨(-220971498469911142), (-220760174845042258)⟩, true⟩

def state01 : KState := ⟨⟨360547827639675295, 360547836070774986⟩, ⟨1250929869917813542, 1251141369978915062⟩, true⟩

def words00 : List Nat := [360581559479746245, 360581559221439386, 360581558767556848, 360581558419800508, 360581558071930926, 360581557375558750, 360581555954143536, 360581553974939221, 360581551995746116, 360581550470397162]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 37100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 37100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360522863629997103, 360522872065803748⟩, ⟨2177488434472310398, 2177700109232513848⟩, true⟩

def words01 : List Nat := [360581549562328184, 360581548526341473, 360581547490356100, 360581546047488783, 360581544999321950, 360581543541029477, 360581542082664139, 360581541349787026, 360581540135795058, 360581538555815400]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 37110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 37100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360581512413209157, 360581520853745029⟩, ⟨83862591732879, 295712922851243⟩, true⟩

def words02 : List Nat := [360581536975814335, 360581535374548925, 360581534245282602, 360581533841227854, 360581533437164112, 360581532319057773, 360581530898644585, 360581530024575751, 360581529150394070, 360581528818003657]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 37120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 37100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360580202883412041, 360580211328704903⟩, ⟨48674782775825040, 48886809758446934⟩, true⟩

def words03 : List Nat := [360581528818234718, 360581528452802935, 360581528226073861, 360581528734140727, 360581528746910390, 360581528759757176, 360581528760202821, 360581528407571257, 360581527648169102, 360581527613297215]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 37130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 37100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360555500476049477, 360555508926061665⟩, ⟨966292309056697191, 966504511338277323⟩, true⟩

def words04 : List Nat := [360581527757954815, 360581527981028598, 360581527981478415, 360581527842727929, 360581527703905911, 360581526910270433, 360581526588838105, 360581526339884349, 360581526090897277, 360581525198237662]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 37140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 37100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk371A
