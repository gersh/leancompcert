import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk468A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360552565926099542, 360552579592024721⟩, ⟨1418444575099195151, 1418876760469147311⟩, true⟩

def state01 : KState := ⟨⟨360558058416971021, 360558072088953757⟩, ⟨1161338739878745209, 1161771208772995563⟩, true⟩

def words00 : List Nat := [360582896824238813, 360582896332722893, 360582895856902849, 360582895153358851, 360582894449744758, 360582893317199297, 360582892472903538, 360582892084021877, 360582891695101896, 360582890956904473]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 46800 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 46800 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360608742353570050, 360608756031621120⟩, ⟨(-1211521576305263745), (-1211088823322494253)⟩, true⟩

def words01 : List Nat := [360582890427231139, 360582890352965784, 360582890315171102, 360582890315814040, 360582890032427935, 360582889359404932, 360582888686270727, 360582888565873998, 360582889118881307, 360582889672010636]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 46810 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 46800 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360598633491642520, 360598647175823175⟩, ⟨(-738403015044039990), (-737969975044029250)⟩, true⟩

def words02 : List Nat := [360582889997384252, 360582890068482848, 360582890128151566, 360582890187997260, 360582890188535953, 360582890129800341, 360582889939009366, 360582889370429954, 360582888801750781, 360582889024704386]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 46820 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 46800 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360550762553254963, 360550776243489030⟩, ⟨1503734224489592486, 1504167548001803158⟩, true⟩

def words03 : List Nat := [360582889816573122, 360582890608531273, 360582891118344562, 360582891173368534, 360582891173909783, 360582890855974182, 360582890537866064, 360582890208686362, 360582889813736382, 360582889128800768]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 46830 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 46800 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360586246890963101, 360586260587263608⟩, ⟨(-158462883585286207), (-158029275890959685)⟩, true⟩

def words04 : List Nat := [360582888443749102, 360582888031635420, 360582888158835698, 360582888398401785, 360582888399000907, 360582888238688659, 360582887789506209, 360582887668230377, 360582887546774504, 360582887569059281]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 46840 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 46800 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk468A
