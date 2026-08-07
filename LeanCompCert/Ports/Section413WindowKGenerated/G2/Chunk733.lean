import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk733

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360559819331707705, 360559854087547823⟩, ⟨1654338613976945162, 1656059363792645188⟩, true⟩

def state01 : KState := ⟨⟨360584095168853031, 360584129934528471⟩, ⟨(-125191204841132532), (-123469734048363686)⟩, true⟩

def words00 : List Nat := [360582446677357349, 360582446456893610, 360582446425612986, 360582446503512129, 360582446504483059, 360582446426380740, 360582446162285233, 360582445953209410, 360582445743833175, 360582445743424157]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 73300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 73300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360584953957413179, 360584988733024547⟩, ⟨(-188199544661821167), (-186477345417339017)⟩, true⟩

def words01 : List Nat := [360582445744368721, 360582445623838802, 360582445532057439, 360582445654919255, 360582445655798339, 360582445627407844, 360582445598904674, 360582445477851475, 360582445396513333, 360582445432395569]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 73310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 73300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360578402556043436, 360578437341461876⟩, ⟨292102560836141598, 293825479184436024⟩, true⟩

def words02 : List Nat := [360582445438356447, 360582445439398763, 360582445319752923, 360582445106159980, 360582444892417823, 360582444546430661, 360582444352277582, 360582444343985398, 360582444335579980, 360582444234673174]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 73320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 73300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360583913990748411, 360583948786022514⟩, ⟨(-112047851395850069), (-110324210284030043)⟩, true⟩

def words03 : List Nat := [360582444311872117, 360582444444046379, 360582444630619228, 360582444712547780, 360582444713509157, 360582444636309318, 360582444558917907, 360582444479276082, 360582444500645008, 360582444522237128]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 73330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 73300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587072687026637, 360587107492236556⟩, ⟨(-343859946078270712), (-342135576225803512)⟩, true⟩

def words04 : List Nat := [360582444523175465, 360582444431185810, 360582444153410002, 360582444010385242, 360582443867088316, 360582443677042420, 360582443584938889, 360582443375201775, 360582443165264232, 360582443130793280]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 73340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 73300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360559710488399650, 360559745303442439⟩, ⟨1663362558228536923, 1665087649370348035⟩, true⟩

def words05 : List Nat := [360582443380753993, 360582443630907698, 360582443738269708, 360582443739312183, 360582443661062177, 360582443472928307, 360582443284493885, 360582443249021973, 360582443098788921, 360582442790484020]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 73350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 73300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360591088864332830, 360591123689208100⟩, ⟨(-638708473602737995), (-636982661101033179)⟩, true⟩

def words06 : List Nat := [360582442481932594, 360582442359177856, 360582442484943928, 360582442641182907, 360582442642144934, 360582442634424105, 360582442441048313, 360582442199971639, 360582441958585035, 360582442021231638]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 73360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 73300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360599912785930923, 360599947620732530⟩, ⟨(-1286187948898678343), (-1284461408052406669)⟩, true⟩

def words07 : List Nat := [360582442022795598, 360582442024480517, 360582442175811337, 360582442469333193, 360582442708801216, 360582442948431603, 360582443082195532, 360582443136381204, 360582443375770169, 360582443615498854]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 73370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 73300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360581772844614872, 360581807689251163⟩, ⟨44895718015160008, 46622980579784768⟩, true⟩

def words08 : List Nat := [360582443757268863, 360582443758311800, 360582443714753919, 360582443561221974, 360582443407528479, 360582443154208802, 360582443032273579, 360582443064638157, 360582443065570174, 360582442966272281]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 73380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 73300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360593561677250262, 360593596531732506⟩, ⟨(-820374314855309857), (-818646329648089395)⟩, true⟩

def words09 : List Nat := [360582443087922386, 360582443218538657, 360582443435224437, 360582443466755290, 360582443467743432, 360582443319979396, 360582443172021377, 360582443158103815, 360582443310901406, 360582443463931685]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 73390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 73300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 73300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk733
