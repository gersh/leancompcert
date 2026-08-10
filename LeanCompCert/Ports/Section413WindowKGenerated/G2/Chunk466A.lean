import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk466A

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360536740272942771, 360536753817514646⟩, ⟨2152602193776476020, 2153028711941213850⟩, true⟩

def state01 : KState := ⟨⟨360583377743621767, 360583391294229056⟩, ⟨(-20902946432863093), (-20476146987781257)⟩, true⟩

def words00 : List Nat := [360582955159460917, 360582954628040396, 360582954329089910, 360582954279062800, 360582954228990620, 360582953781154810, 360582953349474384, 360582952777524311, 360582952205411370, 360582951995630275]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 46600 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 46600 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360597520452105993, 360597534008820812⟩, ⟨(-680278021922674384), (-679850937776414704)⟩, true⟩

def words01 : List Nat := [360582951996205457, 360582951773616999, 360582951550924326, 360582951403876675, 360582951404412113, 360582951376019545, 360582951347558576, 360582951023628656, 360582951190873397, 360582951504417723]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 46610 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 46600 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360570207201757883, 360570220764492638⟩, ⟨593184986236037322, 593612351062568040⟩, true⟩

def words02 : List Nat := [360582952029808062, 360582952096155768, 360582952096725800, 360582951933597183, 360582951770371120, 360582951477272691, 360582951466271971, 360582951444013522, 360582951421695786, 360582951031510922]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 46620 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 46600 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360618042763276047, 360618056332050730⟩, ⟨(-1637752695975974848), (-1637325049477458442)⟩, true⟩

def words03 : List Nat := [360582950759032130, 360582950387540598, 360582950102305088, 360582950205462190, 360582950206052268, 360582949915989158, 360582949686096244, 360582949981041289, 360582950734267900, 360582951487611772]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 46630 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 46600 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360602284759088526, 360602298333965419⟩, ⟨(-902944908734584834), (-902516977599696248)⟩, true⟩

def words04 : List Nat := [360582951884062799, 360582951884703006, 360582952217876827, 360582952614120045, 360582952790955025, 360582952791595360, 360582952630294103, 360582952192396741, 360582951774229291, 360582952189668412]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 46640 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 46600 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk466A
