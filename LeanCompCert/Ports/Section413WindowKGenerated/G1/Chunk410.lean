import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk410

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362478965319105382, 362478989220386361⟩, ⟨249715137870097591, 250377306911093505⟩, true⟩

def state01 : KState := ⟨⟨362483451368816011, 362483475282255499⟩, ⟨65735539841077344, 66398207441807738⟩, true⟩

def words00 : List Nat := [371285095836034748, 371285095684970749, 371285095130950698, 371285095111882962, 371285095170275603, 371285095171647188, 371285094861819654, 371285094551535238, 371285094354297784, 371285094355833695]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 41000 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 41000 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362464431998207922, 362464455923771626⟩, ⟨845937513250237099, 846600678128475523⟩, true⟩

def words01 : List Nat := [371285094871816532, 371285095427786490, 371285095899391664, 371285095900738999, 371285095580576206, 371285095375453687, 371285095556789838, 371285095558137255, 371285095154750444, 371285094653126294]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 41010 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 41000 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362476933621600741, 362476957559224272⟩, ⟨333081681086396294, 333745340719721878⟩, true⟩

def words02 : List Nat := [371285094150919300, 371285093871782810, 371285093406772646, 371285093472173498, 371285093473217575, 371285093427461448, 371285092689547133, 371285092198659256, 371285091736243462, 371285091737647858]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 41020 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 41000 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362490914700302609, 362490938650226862⟩, ⟨(-240643455945815009), (-239979291554545579)⟩, true⟩

def words03 : List Nat := [371285091540420653, 371285091270408018, 371285091196631794, 371285091198142283, 371285091289711561, 371285091398407927, 371285091505900694, 371285091507252687, 371285091199894181, 371285091344080459]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 41030 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 41000 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362459745744969981, 362459769706907064⟩, ⟨1038618849533502389, 1039283506994695291⟩, true⟩

def words04 : List Nat := [371285091422490644, 371285091423838936, 371285090711709292, 371285089999397864, 371285089286616567, 371285088752689072, 371285087921986136, 371285087684856757, 371285087447256269, 371285087210122526]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 41040 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 41000 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362502408709638837, 362502432683753029⟩, ⟨(-712877307709420985), (-712212150315505323)⟩, true⟩

def words05 : List Nat := [371285086594304706, 371285086572071901, 371285087034555460, 371285087035910501, 371285086958765407, 371285086650807504, 371285086625608494, 371285086627108148, 371285087038064028, 371285087462002086]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 41050 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 41000 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362472257312903892, 362472281299190636⟩, ⟨525278345197409045, 525944002458615045⟩, true⟩

def words06 : List Nat := [371285087884697820, 371285087886070476, 371285088072865212, 371285088320282823, 371285088708778882, 371285088710127930, 371285088309019515, 371285087903256950, 371285087496994060, 371285087337721404]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 41060 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 41000 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362482669689693901, 362482693688154091⟩, ⟨97653461041311256, 98319618326004106⟩, true⟩

def words07 : List Nat := [371285087212532264, 371285087399706100, 371285087585810093, 371285087587168328, 371285087242236456, 371285087021503739, 371285087169746447, 371285087171100968, 371285087114363908, 371285087057636224]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 41070 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 41000 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362493948397687627, 362493972408235267⟩, ⟨(-365667575288701015), (-365000921389873295)⟩, true⟩

def words08 : List Nat := [371285087533953533, 371285087812439407, 371285088336777240, 371285088861609933, 371285089223535180, 371285089224884795, 371285088886650395, 371285088977133569, 371285089444502386, 371285089662101324]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 41080 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 41000 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362484162303413898, 362484186326234735⟩, ⟨36524328354395188, 37191486621733248⟩, true⟩

def words09 : List Nat := [371285089878916121, 371285090096163528, 371285090585687691, 371285090783324601, 371285091158569380, 371285091534333985, 371285091785190580, 371285091786540614, 371285091248945284, 371285091228585629]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 41090 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 41000 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 41000 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk410
