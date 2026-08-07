import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk282

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362479227988882273, 362479238950983423⟩, ⟨165280201579646147, 165489171540159829⟩, true⟩

def state01 : KState := ⟨⟨362476626975916097, 362476637946041573⟩, ⟨238644713883909254, 238853910171611196⟩, true⟩

def words00 : List Nat := [371285108201357143, 371285108202256236, 371285107759863490, 371285106997663520, 371285106235176260, 371285105849778902, 371285104873407591, 371285104906404877, 371285104939424207, 371285104940375909]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 28200 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 28200 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362512692628385480, 362512703606620102⟩, ⟨(-778895780779655076), (-778686355690688370)⟩, true⟩

def words01 : List Nat := [371285105595354027, 371285106550849819, 371285108595928077, 371285108968829890, 371285109048808693, 371285109129055450, 371285109480794408, 371285109481785261, 371285110184081935, 371285111162848064]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 28210 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 28200 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362491654792442709, 362491665778801668⟩, ⟨(-185257722512620966), (-185048068114710452)⟩, true⟩

def words02 : List Nat := [371285112034758892, 371285112035658816, 371285111539605396, 371285111672407937, 371285112200205421, 371285112201111336, 371285111610348661, 371285110910501093, 371285110762964946, 371285110996182749]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 28220 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 28200 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362452258897901976, 362452269892383561⟩, ⟨927158148066548073, 927368031808230063⟩, true⟩

def words03 : List Nat := [371285111542335127, 371285112088810607, 371285112629090584, 371285112629992690, 371285111885552755, 371285111517208814, 371285111148436963, 371285111027593333, 371285109865574227, 371285108703708216]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 28230 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 28200 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362469272155732131, 362469283158272999⟩, ⟨446770780473451017, 446980891849960031⟩, true⟩

def words04 : List Nat := [371285107541514132, 371285107415242070, 371285106976627735, 371285107289136336, 371285107289845732, 371285107290310791, 371285105949687950, 371285105636289667, 371285105489794584, 371285105490727865]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 28240 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 28200 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362453246136932787, 362453257147688626⟩, ⟨899733000197046183, 899943343688422331⟩, true⟩

def words05 : List Nat := [371285104931345852, 371285104360636636, 371285104126669756, 371285104127664703, 371285104200006823, 371285104424821974, 371285104650057761, 371285104650958988, 371285103402410505, 371285102276623107]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 28250 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 28200 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362457102781028548, 362457113799809745⟩, ⟨790772625050296483, 790983195380686027⟩, true⟩

def words06 : List Nat := [371285101150413008, 371285101044060308, 371285099747957573, 371285098453202364, 371285097158187010, 371285096239809557, 371285094871114096, 371285094389428989, 371285093907489477, 371285093396392012]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 28260 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 28200 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362501865912783617, 362501876939735452⟩, ⟨(-474988398307006981), (-474777596952354119)⟩, true⟩

def words07 : List Nat := [371285092407313708, 371285092213855161, 371285092308979246, 371285092309881101, 371285091144488670, 371285089860520483, 371285088576285871, 371285088541110344, 371285088480530973, 371285089075199108]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 28270 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 28200 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362473924914329867, 362473935949414450⟩, ⟨315195347515031810, 315406378905404710⟩, true⟩

def words08 : List Nat := [371285089424116185, 371285089425018155, 371285088432603635, 371285088561361058, 371285089065580799, 371285089066482785, 371285087907040740, 371285086519034506, 371285085130740845, 371285084990733129]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 28280 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 28200 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362475990449318917, 362476001492517995⟩, ⟨256901403697333540, 257112664688380596⟩, true⟩

def words09 : List Nat := [371285085111175734, 371285085626029122, 371285086141857706, 371285086142776336, 371285085952815873, 371285086046627947, 371285087386863679, 371285087387766266, 371285087065726451, 371285086745687196]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 28290 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 28200 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 28200 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk282
