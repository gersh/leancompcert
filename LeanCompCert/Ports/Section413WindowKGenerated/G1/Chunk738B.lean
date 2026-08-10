import LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk738A

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk738B

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables
open LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk738A

def state06 : KState := ⟨⟨362476680350025581, 362476761650392563⟩, ⟨625972705606568148, 630027927024244586⟩, true⟩

def words05 : List Nat := [371285292361048992, 371285292303598583, 371285292245152515, 371285292239990124, 371285292169053556, 371285292155069330, 371285292140224494, 371285292088416076, 371285291791565098, 371285291679190617]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 73850 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 73800 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362469706502442071, 362469787825406137⟩, ⟨1141102960445459581, 1145159851001448035⟩, true⟩

def words06 : List Nat := [371285291617612868, 371285291620151666, 371285291430054803, 371285291230874472, 371285291030672959, 371285290808819970, 371285290516800746, 371285290408825847, 371285290300018592, 371285290192415769]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 73860 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 73800 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485443312169006, 362485524658161299⟩, ⟨(-21480054031557721), (-17421462269078419)⟩, true⟩

def words07 : List Nat := [371285289984311097, 371285289834138418, 371285289683234245, 371285289685774605, 371285289474402503, 371285289242414487, 371285289009399140, 371285288960491957, 371285288847728338, 371285288853796590]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 73870 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 73800 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362474600154965547, 362474681523863920⟩, ⟨779657974654182079, 783718258836016387⟩, true⟩

def words08 : List Nat := [371285288857735786, 371285288860284194, 371285288751106226, 371285288790141164, 371285288835884823, 371285288838424802, 371285288640218125, 371285288405871217, 371285288170461618, 371285288077644351]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 73880 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 73800 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362468099837410894, 362468181229191372⟩, ⟨1260044745276408332, 1264106720333203062⟩, true⟩

def words09 : List Nat := [371285287935827420, 371285287930440109, 371285287924153663, 371285287918976819, 371285287669056671, 371285287476358478, 371285287282325648, 371285287271993906, 371285287096807444, 371285286868167465]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 73890 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 73800 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 73800 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk738B
