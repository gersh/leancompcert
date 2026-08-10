import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk213A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360584103667229535, 360584106315309487⟩, ⟨(-74740352587977359), (-74702186407148533)⟩, true⟩

def state01 : KState := ⟨⟨360479739429141278, 360479742079808676⟩, ⟨2148502574579468487, 2148540795886066099⟩, true⟩

def words00 : List Nat := [360580599335281203, 360580598479136392, 360580595428310719, 360580591221438887, 360580587014917315, 360580582261731142, 360580578926533366, 360580574717894992, 360580570509617035, 360580565204908914]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 21300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 21300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360603806956260645, 360603809609520879⟩, ⟨(-496232061884262082), (-496193785311878796)⟩, true⟩

def words01 : List Nat := [360580560474094398, 360580557260444296, 360580554047012855, 360580553023389160, 360580549807212511, 360580544469593628, 360580539132423122, 360580535984675492, 360580535979530192, 360580537071398283]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 21310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 21300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360552973095383240, 360552975751263488⟩, ⟨587765284046004911, 587803616489927317⟩, true⟩

def words02 : List Nat := [360580537071645578, 360580536692396879, 360580538286381903, 360580540177412135, 360580541455937613, 360580541456212384, 360580540544669801, 360580538538821792, 360580536533114397, 360580533351661516]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 21320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 21300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360448756875865326, 360448759534333849⟩, ⟨2811380994130947919, 2811419381795895705⟩, true⟩

def words03 : List Nat := [360580532341516863, 360580532623302083, 360580532623548064, 360580531459210700, 360580528106205732, 360580523380464834, 360580518655082109, 360580514881953313, 360580509821399127, 360580503647820068]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 21330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 21300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360571384788178334, 360571387449244580⟩, ⟨193787073679362039, 193825516792806777⟩, true⟩

def words04 : List Nat := [360580497474755793, 360580493486803125, 360580490607753858, 360580487669254429, 360580484731008175, 360580479884272108, 360580474457513304, 360580471214725212, 360580467972158105, 360580465927782885]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 21340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 21300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk213A
