import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk183

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360682528764351688, 360682530692666497⟩, ⟨(-1793474626494340064), (-1793450741008467516)⟩, true⟩

def state01 : KState := ⟨⟨360674970703004747, 360674972633513806⟩, ⟨(-1655175827479406257), (-1655151901827514009)⟩, true⟩

def words00 : List Nat := [360584541607963240, 360584546977542166, 360584550847636552, 360584554717336171, 360584556520191985, 360584559830888652, 360584566117845947, 360584572404161234, 360584576570911740, 360584581507861056]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 18300 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 18300 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360720383910128931, 360720385842841571⟩, ⟨(-2486774415578156018), (-2486750449567729598)⟩, true⟩

def words01 : List Nat := [360584589420166939, 360584597331680849, 360584608217882505, 360584616144177481, 360584620916089893, 360584625687496596, 360584631261616197, 360584638779273383, 360584646189239595, 360584653598446193]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 18310 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 18300 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360765418793928545, 360765420728863317⟩, ⟨(-3312667550721744264), (-3312643543991386094)⟩, true⟩

def words02 : List Nat := [360584659378008343, 360584662199665258, 360584667038353077, 360584671876582982, 360584675907703583, 360584682230551054, 360584686571432947, 360584690911866782, 360584698222104728, 360584708081217723]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 18320 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 18300 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360630378615629497, 360630380552764717⟩, ⟨(-836543025553579292), (-836518978477863744)⟩, true⟩

def words03 : List Nat := [360584719250783742, 360584730419175504, 360584739059575569, 360584745871598028, 360584751220733772, 360584756569347167, 360584762359947191, 360584766343331292, 360584768830682725, 360584771317800546]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 18330 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 18300 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360646126474433766, 360646128413773121⟩, ⟨(-1125318239962681083), (-1125294152452008603)⟩, true⟩

def words04 : List Nat := [360584776770756707, 360584783734010327, 360584789977470723, 360584796220293623, 360584799927316113, 360584800685372279, 360584801338489879, 360584801991602782, 360584804481517353, 360584807823480930]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 18340 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 18300 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360645619855763992, 360645621797332272⟩, ⟨(-1115841918135967641), (-1115817789713895795)⟩, true⟩

def words05 : List Nat := [360584809660047046, 360584811496436945, 360584816295076694, 360584823570268572, 360584830081427055, 360584836591915301, 360584841231143949, 360584844097122032, 360584847407644807, 360584850717885952]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 18350 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 18300 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360613630595524041, 360613632539297073⟩, ⟨(-528829190305660932), (-528805021393032826)⟩, true⟩

def words06 : List Nat := [360584852989079532, 360584852989313476, 360584852317202739, 360584850152001847, 360584847986998713, 360584845061591258, 360584845142300031, 360584846661576725, 360584846661788037, 360584847768658946]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 18360 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 18300 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360653931207096667, 360653933153076074⟩, ⟨(-1269418832282118725), (-1269394622827195937)⟩, true⟩

def words07 : List Nat := [360584852292389161, 360584856815695082, 360584862563293083, 360584865370428722, 360584865376137589, 360584865381860326, 360584865382050597, 360584865487220447, 360584869245171937, 360584873002767212]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 18370 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 18300 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360624137503090185, 360624139451301273⟩, ⟨(-721750133233704159), (-721725882749292661)⟩, true⟩

def words08 : List Nat := [360584874450450432, 360584877398082794, 360584881996891278, 360584886595267527, 360584890434930638, 360584892811819391, 360584893554176217, 360584894296475827, 360584894296668751, 360584896023388202]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 18380 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 18300 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360558496274619506, 360558498225038190⟩, ⟨485948984457371304, 485973275550597802⟩, true⟩

def words09 : List Nat := [360584900017130395, 360584904010484999, 360584906515765241, 360584908146413794, 360584908181473402, 360584908216596725, 360584911200284050, 360584911251139389, 360584911251348202, 360584909816100723]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 18390 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 18300 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 18300 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk183
