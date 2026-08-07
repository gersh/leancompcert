import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk024

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨361497986317895293, 361497986344706839⟩, ⟨(-2285901282785100176), (-2285901239027559186)⟩, true⟩

def state01 : KState := ⟨⟨360749203268527734, 360749203295575793⟩, ⟨(-486647789008068934), (-486647744681687272)⟩, true⟩

def words00 : List Nat := [360546316937580246, 360546541659624092, 360546672076955606, 360546802385834453, 360546812591863382, 360546910982880391, 360547076271127387, 360547241422153893, 360547274770785613, 360547358523828930]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 2400 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 2400 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨361638142136777487, 361638142164064181⟩, ⟨(-2633798217634207497), (-2633798172731546139)⟩, true⟩

def words01 : List Nat := [360547612181255479, 360547865628447093, 360548172469702858, 360548452579775124, 360548563323066055, 360548673974721632, 360548953599977460, 360549345895835513, 360549795811669422, 360550245355831407]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 2410 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 2400 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨361409378471979317, 361409378499507995⟩, ⟨(-2079778149227858144), (-2079778103738380294)⟩, true⟩

def words02 : List Nat := [360550604915215944, 360550978553499476, 360551520118226907, 360552061236310293, 360552536995811604, 360552848442070602, 360553071481076033, 360553294336437445, 360553502736623585, 360553854804017095]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 2420 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 2400 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360529751582923777, 360529751610692834⟩, ⟨60661453004001033, 60661499078830711⟩, true⟩

def words03 : List Nat := [360554105394102723, 360554355778200264, 360554518662868693, 360554518662894190, 360554518290413841, 360554471957911368, 360554545521482262, 360554623073980395, 360554623074003396, 360554612880807109]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 2430 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 2400 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨361355962458520465, 361355962486531847⟩, ⟨(-1959313181427261221), (-1959313134759977449)⟩, true⟩

def words04 : List Nat := [360554758227718508, 360555057742628623, 360555343714173667, 360555629451799761, 360555768448066724, 360555768448092369, 360555887777985350, 360556029835718290, 360556242839664065, 360556569122696687]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 2440 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 2400 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360885261753247565, 360885261781504083⟩, ⟨(-804329276235504942), (-804329228966405474)⟩, true⟩

def words05 : List Nat := [360556785526139104, 360557001753144427, 360557226731555149, 360557536836919014, 360557801537001429, 360558066021621910, 360558196030936637, 360558196030962409, 360558298680268979, 360558431538120741]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 2450 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 2400 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360809796666421423, 360809796694921683⟩, ⟨(-620905013917875168), (-620904966047929102)⟩, true⟩

def words06 : List Nat := [360558620760633600, 360558649861521749, 360558649861544809, 360558593284891174, 360558536754136924, 360558361304575440, 360558351196134032, 360558427219824131, 360558427219847270, 360558519897654209]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 2460 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 2400 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨361266660741013931, 361266660769759650⟩, ⟨(-1753741007616267523), (-1753740959138801013)⟩, true⟩

def words07 : List Nat := [360558609483307946, 360558698996517773, 360558949778449155, 360559041478359110, 360559041478383432, 360558972493140089, 360558995641840117, 360559221899546706, 360559507157176790, 360559792184858884]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 2470 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 2400 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨361005070650452518, 361005070679446796⟩, ⟨(-1106323477129647186), (-1106323428034506132)⟩, true⟩

def words08 : List Nat := [360559993163068718, 360560166054541095, 360560372715841202, 360560579210821978, 360560664471633382, 360560738814997605, 360560738815020924, 360560730091901663, 360560764081812895, 360560942446594727]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 2480 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 2400 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360041898164349376, 360041898193591126⟩, ⟨1299535735044982619, 1299535784757592891⟩, true⟩

def words09 : List Nat := [360561192476641330, 360561442306107609, 360561609237504157, 360561733537925524, 360561814011844036, 360561894421312998, 360561985359693831, 360561985359720108, 360561920516396123, 360561712507494164]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 2490 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 2400 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 2400 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk024
