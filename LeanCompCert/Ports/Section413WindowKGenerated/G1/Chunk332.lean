import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk332

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362524112191882650, 362524127594713495⟩, ⟨(-1310573781174953941), (-1310228154993277447)⟩, true⟩

def state01 : KState := ⟨⟨362491333983910643, 362491349396438948⟩, ⟨(-222213921646677827), (-221867973459869221)⟩, true⟩

def words00 : List Nat := [371284665060578490, 371284665178290772, 371284666201836159, 371284667225862704, 371284668381728086, 371284668382801135, 371284668330688106, 371284668278172673, 371284668637194397, 371284668839591522]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 33200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 33200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362474990940579192, 362475006362758309⟩, ⟨320744276088646655, 321090544827888275⟩, true⟩

def words01 : List Nat := [371284669947193128, 371284671055158105, 371284672162064227, 371284672163137389, 371284672062621779, 371284671977718335, 371284672521201375, 371284672522277561, 371284672231835115, 371284671942072815]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 33210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 33200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362496552618836812, 362496568050627884⟩, ⟨(-395456303585769656), (-395109715488507722)⟩, true⟩

def words02 : List Nat := [371284672165415864, 371284672382585330, 371284673504205271, 371284674626202900, 371284675616676121, 371284675617750196, 371284676267129597, 371284676964415157, 371284677898584179, 371284678257498322]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 33220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 33200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362489910658909225, 362489926100489558⟩, ⟨(-174666711453130073), (-174319798009362733)⟩, true⟩

def words03 : List Nat := [371284678460070199, 371284678662999367, 371284679691590846, 371284680369496396, 371284680996067962, 371284681623019371, 371284682245489611, 371284682246563615, 371284681821232580, 371284681980336454]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 33230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 33200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362488931005111329, 362488946456275274⟩, ⟨(-142105057504428691), (-141757825451514969)⟩, true⟩

def words04 : List Nat := [371284682737278933, 371284682738360239, 371284682685887216, 371284682458967120, 371284682231660096, 371284682216445026, 371284682186936206, 371284682624786331, 371284683061893905, 371284683191247109]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 33240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 33200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362519628939318419, 362519644400170064⟩, ⟨(-1162965230716177891), (-1162617676497391173)⟩, true⟩

def words05 : List Nat := [371284683996567252, 371284684802385556, 371284686072879872, 371284686482262568, 371284686749173044, 371284687016403256, 371284687656276737, 371284687914991285, 371284688966727687, 371284690018867717]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 33250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 33200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362465181094802720, 362465196565361014⟩, ⟨648183834079427056, 648531711188960202⟩, true⟩

def words06 : List Nat := [371284691070708870, 371284691071783639, 371284691174034082, 371284691429455793, 371284691960112199, 371284691961187067, 371284691288602585, 371284690599741221, 371284689910498258, 371284689553373908]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 33260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 33200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362441611398093210, 362441626878349819⟩, ⟨1432486956596531953, 1432835156418172269⟩, true⟩

def words07 : List Nat := [371284688968231480, 371284688652887309, 371284688337197945, 371284688021097350, 371284686636224729, 371284685293375622, 371284683950062763, 371284683404988391, 371284682111846169, 371284680819347962]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 33270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 33200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362490321389444333, 362490336879320288⟩, ⟨(-188794331567399185), (-188445811564964007)⟩, true⟩

def words08 : List Nat := [371284679526429824, 371284678868827000, 371284677797722635, 371284677526769656, 371284677255522454, 371284676770577014, 371284675713147404, 371284675557360822, 371284676144906728, 371284676316057996]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 33280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 33200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362467376277831904, 362467391777520056⟩, ⟨575288207695838548, 575637054394819272⟩, true⟩

def words09 : List Nat := [371284676467589747, 371284676619478488, 371284677359004538, 371284677718166804, 371284678352648703, 371284678987517787, 371284679440399879, 371284679441476014, 371284678693342762, 371284678175549931]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 33290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 33200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 33200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk332
