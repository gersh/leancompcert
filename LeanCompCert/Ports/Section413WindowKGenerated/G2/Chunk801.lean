import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk801

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨360571570782853551, 360571612577173063⟩, ⟨843193629587168216, 845454609520948944⟩, true⟩

def state01 : KState := ⟨⟨360573124836325491, 360573166641452719⟩, ⟨718673834985824953, 720935680670266903⟩, true⟩

def words00 : List Nat := [360582167435227301, 360582167300680691, 360582167152061860, 360582166925636174, 360582166699023500, 360582166397718837, 360582166199299421, 360582166156745115, 360582166114059712, 360582165963393429]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG2 2 16 37273 0 80100 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG2 2 16 37273 0 80100 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨360589100458270807, 360589142274204388⟩, ⟨(-561221665548602367), (-558958954112798005)⟩, true⟩

def words01 : List Nat := [360582165895260374, 360582165939798159, 360582166007948379, 360582166009094534, 360582165987087623, 360582165822956629, 360582165658610437, 360582165662867399, 360582165750875166, 360582165839136019]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG2 2 16 37273 0 80110 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG2 2 16 37273 0 80100 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨360577008796180413, 360577050623036545⟩, ⟨407587242739390470, 409850829344417128⟩, true⟩

def words02 : List Nat := [360582165840159758, 360582165852758752, 360582165955589135, 360582166058759793, 360582166119773012, 360582166120918832, 360582166026569238, 360582165834631415, 360582165642495165, 360582165446814711]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG2 2 16 37273 0 80120 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG2 2 16 37273 0 80100 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨360561223776272273, 360561265613923660⟩, ⟨1672554560876675844, 1674819012558277952⟩, true⟩

def words03 : List Nat := [360582165444074479, 360582165505390227, 360582165506411311, 360582165489852258, 360582165356827278, 360582165103694543, 360582164850196334, 360582164720436464, 360582164538510717, 360582164278916901]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG2 2 16 37273 0 80130 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG2 2 16 37273 0 80100 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨360602293920143955, 360602335768628171⟩, ⟨(-1619056902261415190), (-1616791582384449274)⟩, true⟩

def words04 : List Nat := [360582164019069827, 360582163922006184, 360582163922949028, 360582163913929234, 360582163904835821, 360582163757859488, 360582163586912910, 360582163571752536, 360582163695275153, 360582163948159501]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG2 2 16 37273 0 80140 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG2 2 16 37273 0 80100 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨360597971269546637, 360598013128944641⟩, ⟨(-1272569627276887292), (-1270303432606534992)⟩, true⟩

def words05 : List Nat := [360582164123032105, 360582164298025635, 360582164628221999, 360582165053886568, 360582165333939458, 360582165614168851, 360582165745026137, 360582165830303907, 360582166028926727, 360582166227925361]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG2 2 16 37273 0 80150 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG2 2 16 37273 0 80100 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨360601415616650076, 360601457486835719⟩, ⟨(-1548727509886550125), (-1546460450423496325)⟩, true⟩

def words06 : List Nat := [360582166495589059, 360582166647970888, 360582166722763788, 360582166797689403, 360582166833580699, 360582166958476857, 360582167238393227, 360582167518529883, 360582167720768999, 360582167962563558]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG2 2 16 37273 0 80160 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG2 2 16 37273 0 80100 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨360606057090874890, 360606098971903892⟩, ⟨(-1920913140063705447), (-1918645211237136415)⟩, true⟩

def words07 : List Nat := [360582168139405459, 360582168316574171, 360582168648728257, 360582168825872239, 360582168871973297, 360582168918160908, 360582169119457873, 360582169446947397, 360582169746328760, 360582170045958380]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG2 2 16 37273 0 80170 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG2 2 16 37273 0 80100 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨360583538618381567, 360583580510339713⟩, ⟨(-115341410907225506), (-113072605730449804)⟩, true⟩

def words08 : List Nat := [360582170247084916, 360582170345440889, 360582170574087573, 360582170803071165, 360582170903658578, 360582170904805340, 360582170850264413, 360582170718140980, 360582170585804144, 360582170469241206]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG2 2 16 37273 0 80180 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG2 2 16 37273 0 80100 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨360551969133875153, 360552011036641409⟩, ⟨2416481774157100310, 2418751446090001178⟩, true⟩

def words09 : List Nat := [360582170643028957, 360582170817051973, 360582170913234693, 360582170914381636, 360582170898503300, 360582170815499626, 360582170732166052, 360582170647237294, 360582170407091865, 360582170032228567]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG2 2 16 37273 0 80190 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG2 2 16 37273 0 80100 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG2 2 16 37273 0 80100 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G2.Chunk801
