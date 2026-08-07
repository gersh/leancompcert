import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk992

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360592035365492384, 360592100539937279⟩, ⟨(-963292316780422127), (-958926773474869695)⟩, true⟩

def state01 : KState := ⟨⟨360568913987461244, 360568979175629228⟩, ⟨1330406004755724221, 1334772909460454633⟩, true⟩

def words00 : List Nat := [360582434075497925, 360582434076940060, 360582434034719059, 360582434018580734, 360582434002032532, 360582433959964525, 360582433816456505, 360582433614839317, 360582433412958705, 360582433191448808]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 99200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 99200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360558399325183636, 360558464526955603⟩, ⟨2373593385887710105, 2377961640311224657⟩, true⟩

def words01 : List Nat := [360582433057024737, 360582432920385582, 360582432783587739, 360582432596073648, 360582432326787477, 360582432032173428, 360582431737119055, 360582431511949502, 360582431322539927, 360582431082491899]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 99210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 99200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360571699532061478, 360571764747434671⟩, ⟨1053943364489994809, 1058312968493276901⟩, true⟩

def words02 : List Nat := [360582430842110457, 360582430688174798, 360582430610221105, 360582430622865774, 360582430624235177, 360582430540815261, 360582430355856885, 360582430243463653, 360582430130657771, 360582429999560977]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 99220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 99200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360566732829558476, 360566798058679926⟩, ⟨1546827980821442335, 1551198949132244627⟩, true⟩

def words03 : List Nat := [360582429893376687, 360582429702563629, 360582429511452615, 360582429422287379, 360582429402258430, 360582429339174504, 360582429275937090, 360582429151849736, 360582428997986042, 360582428842125435]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 99230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 99200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360583923402028619, 360583988644737135⟩, ⟨(-159228042111396036), (-154855725352719508)⟩, true⟩

def words04 : List Nat := [360582428685788211, 360582428631236907, 360582428612510453, 360582428543004406, 360582428473265489, 360582428350210560, 360582428355212322, 360582428395123557, 360582428396408751, 360582428401259964]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 99240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 99200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360596313449973200, 360596378706318185⟩, ⟨(-1389062377392521033), (-1384688707146278133)⟩, true⟩

def words05 : List Nat := [360582428519615157, 360582428638408280, 360582428704189500, 360582428705632413, 360582428670346370, 360582428548473458, 360582428426323199, 360582428445145028, 360582428586853953, 360582428728913704]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 99250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 99200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360581194434561209, 360581259704660375⟩, ⟨111645660032676166, 116020695585878168⟩, true⟩

def words06 : List Nat := [360582428805804031, 360582428821612881, 360582428871795612, 360582428922409438, 360582428946911895, 360582428948355000, 360582428871771709, 360582428705471623, 360582428538889318, 360582428443409100]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 99260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 99200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360569678244344527, 360569743528026218⟩, ⟨1254958067953800123, 1259334451913514045⟩, true⟩

def words07 : List Nat := [360582428479888129, 360582428528415550, 360582428529701159, 360582428528471050, 360582428529691038, 360582428454185044, 360582428402575194, 360582428404018468, 360582428328468934, 360582428202199401]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 99270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 99200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360587086667656413, 360587151964977371⟩, ⟨(-473488935375758551), (-469111197239961961)⟩, true⟩

def words08 : List Nat := [360582428075626691, 360582427908011459, 360582427790596642, 360582427749714833, 360582427708721552, 360582427581696617, 360582427438860431, 360582427361624643, 360582427306445679, 360582427355523947]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 99280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 99200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360578113000465711, 360578178311531839⟩, ⟨417553494068823075, 421932597027897365⟩, true⟩

def words09 : List Nat := [360582427356811616, 360582427340347638, 360582427366854965, 360582427487703576, 360582427539325862, 360582427591163061, 360582427592473707, 360582427546596702, 360582427422130070, 360582427380988314]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 99290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 99200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 99200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk992
