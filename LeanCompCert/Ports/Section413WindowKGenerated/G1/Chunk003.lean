import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk003

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨363297956301138701, 363297956301890753⟩, ⟨(-259017119865512800), (-259017119711038714)⟩, true⟩

def state01 : KState := ⟨⟨360651954157574424, 360651954158380507⟩, ⟨543488561645119542, 543488561816087082⟩, true⟩

def words00 : List Nat := [371243723426898759, 371243723426904724, 371236062158430403, 371227874413214430, 371219740358128814, 371214254120773960, 371204745831064357, 371205079017519265, 371205143067458324, 371205143067464659]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨364638170326860526, 364638170327723385⟩, ⟨(-703604635309054070), (-703604635120192286)⟩, true⟩

def words01 : List Nat := [371203814619824443, 371208095903191701, 371222198827761576, 371223313261989869, 371223313261994860, 371221934274662759, 371228825878660508, 371232513164325599, 371239405842965614, 371246255576570139]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨361131652524764953, 361131652525686775⟩, ⟨434022512395851520, 434022512603888218⟩, true⟩

def words02 : List Nat := [371252885899681777, 371252921428531232, 371257135449796958, 371261323538627286, 371267293296453143, 371267293296459648, 371261314327744468, 371255413477452615, 371249548498588651, 371246872260850073]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360701460215932704, 360701460216915750⟩, ⟨587957575141578170, 587957575370140244⟩, true⟩

def words03 : List Nat := [371247604470913456, 371252281892135661, 371256114486699967, 371256114486706731, 371248595418677131, 371243308351730075, 371241153349595616, 371241153349602451, 371235848344843678, 371230747203298516]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨361942276168090996, 361942276169136520⟩, ⟨157526188107946775, 157526188358077921⟩, true⟩

def words04 : List Nat := [371225675980469337, 371224399344493446, 371219832192131444, 371218822905840906, 371217819470483333, 371214824199690455, 371201314543567484, 371195702182255811, 371192350993009363, 371192350993016743]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362295463793503882, 362295463794614724⟩, ⟨37754454172402889, 37754454445729073⟩, true⟩

def words05 : List Nat := [371191068728566638, 371189724114740051, 371194705572850567, 371197199337029818, 371201717144587738, 371206209642301991, 371208386872941439, 371208386872948668, 371200629405875156, 371200337279186194]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360638649808630022, 360638649809806671⟩, ⟨643631928797295792, 643631929094660364⟩, true⟩

def words06 : List Nat := [371205419557519676, 371205419557526953, 371201029327511316, 371195216185083919, 371189434895489003, 371185806094691242, 371178745427311412, 371178785750269452, 371178785750275113, 371178195564116564]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨364740196597171131, 364740196598416789⟩, ⟨(-897234123072999740), (-897234122749745200)⟩, true⟩

def words07 : List Nat := [371173506761549556, 371171344427715647, 371173957875316068, 371173957875323759, 371173799051851993, 371172515327381746, 371173309147522859, 371173309147531466, 371179054170119445, 371185251394349217]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362120292425216790, 362120292426533077⟩, ⟨102199648449581431, 102199648800040829⟩, true⟩

def words08 : List Nat := [371191253276628146, 371191253276635926, 371192294052374883, 371196081185913131, 371199035275518770, 371199035275526641, 371193378327950166, 371187539010033031, 371182342808062601, 371182342808071644]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨359296073113043532, 359296073114433170⟩, ⟨1225565292096187756, 1225565292475630264⟩, true⟩

def words09 : List Nat := [371183720454941648, 371185757885753443, 371187697573717947, 371187697573726059, 371181389924637577, 371176923517750304, 371174115050982665, 371174115050990838, 371167665326142294, 371159986345622246]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk003
