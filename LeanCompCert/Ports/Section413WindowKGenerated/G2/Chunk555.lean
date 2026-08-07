import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk555

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360575188914403682, 360575208402779411⟩, ⟨369667482426331836, 370398259715201798⟩, true⟩

def state01 : KState := ⟨⟨360584428984331246, 360584448479989873⟩, ⟨(-143293659244365149), (-142562477718890933)⟩, true⟩

def words00 : List Nat := [360581882329184439, 360581882329956676, 360581882210606194, 360581881840812180, 360581881470907325, 360581880911402910, 360581880621947118, 360581880551700628, 360581880481372451, 360581880295707139]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 55500 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 55500 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360600007515847757, 360600027018789736⟩, ⟨(-1008111084988694295), (-1007379499127486405)⟩, true⟩

def words01 : List Nat := [360581880666232663, 360581881036980050, 360581881613492780, 360581881999927210, 360581882109730271, 360581882219589604, 360581882220229506, 360581882247122377, 360581882574562082, 360581882902164901]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 55510 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 55500 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360599850207176049, 360599869717482141⟩, ⟨(-999502224794835880), (-998770230042639490)⟩, true⟩

def words02 : List Nat := [360581883054255057, 360581883280674350, 360581883604523201, 360581883928598782, 360581884167372663, 360581884168145212, 360581884083648642, 360581883807868545, 360581883578828842, 360581883903611643]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 55520 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 55500 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360546661326557791, 360546680844150298⟩, ⟨1954366931739062491, 1955099331142257395⟩, true⟩

def words03 : List Nat := [360581884220548606, 360581884537611282, 360581884674888911, 360581884675661581, 360581884489659975, 360581884151845732, 360581883813814723, 360581883463540357, 360581883121589932, 360581882488571297]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 55530 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 55500 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360587272080813149, 360587291605696905⟩, ⟨(-301339660042039064), (-300606855646895076)⟩, true⟩

def words04 : List Nat := [360581881855400433, 360581881545790991, 360581881478798331, 360581881559788852, 360581881560514833, 360581881321649903, 360581880759566679, 360581880520980558, 360581880282171482, 360581880238563156]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 55540 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 55500 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360565530131062514, 360565549663307807⟩, ⟨906608480680136011, 907341694045450267⟩, true⟩

def words05 : List Nat := [360581880239251673, 360581880175921591, 360581880288567780, 360581880647578338, 360581880847819232, 360581881048182782, 360581881085419351, 360581881086192314, 360581880800388637, 360581880507333104]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 55550 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 55500 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360573571220917584, 360573590760441922⟩, ⟨459752398432602617, 460486016257377709⟩, true⟩

def words06 : List Nat := [360581880214035897, 360581879970726187, 360581879633175342, 360581879134289632, 360581878635295142, 360581878055047433, 360581877723546960, 360581877654237458, 360581877584844985, 360581877354220173]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 55560 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 55500 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360597114555416470, 360597134102250043⟩, ⟨(-848777947017039542), (-848043922983354682)⟩, true⟩

def words07 : List Nat := [360581877282587642, 360581877360301890, 360581877360939595, 360581877303100071, 360581877063421732, 360581876558429258, 360581876053306950, 360581875797480779, 360581876024376040, 360581876299709906]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 55570 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 55500 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360563007814456930, 360563027368650925⟩, ⟨1046830360486351294, 1047564793649202882⟩, true⟩

def words08 : List Nat := [360581876373389313, 360581876374162616, 360581876125102840, 360581875818839983, 360581875512375447, 360581875124667733, 360581874414247132, 360581873452364194, 360581872490364149, 360581871851357333]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 55580 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 55500 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360551232321190613, 360551251882665143⟩, ⟨1701583477380942304, 1702318315304326724⟩, true⟩

def words09 : List Nat := [360581871512999169, 360581871327690703, 360581871142312202, 360581870740499935, 360581870566179163, 360581870310770286, 360581870055143548, 360581870023090627, 360581869668429890, 360581869118551912]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 55590 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 55500 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 55500 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk555
