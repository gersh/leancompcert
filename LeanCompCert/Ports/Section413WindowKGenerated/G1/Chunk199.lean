import LeanCompCert.Ports.Section413WindowRuntime
import LeanCompCert.Ports.Section413WindowDirectTables

namespace LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk199

open LeanCompCert.Ports.Section413Sweep
open LeanCompCert.Ports.Section413WindowRuntime
open LeanCompCert.Ports.Section413WindowDirectTables

def state00 : KState := ⟨⟨362401453381003440, 362401458680675514⟩, ⟨1663612565655928416, 1663683893835076986⟩, true⟩

def state01 : KState := ⟨⟨362424335660350665, 362424340965559150⟩, ⟨1208149391076430779, 1208220829458003395⟩, true⟩

def words00 : List Nat := [371285056685917569, 371285053557286655, 371285049371699555, 371285046843101274, 371285044314556702, 371285041372716705, 371285035587488841, 371285031392429682, 371285027197461012, 371285025085572109]

set_option maxRecDepth 100000 in
theorem micro00 :
    trace directG1 1 40 36393 8800000000000000 19900 10 state00 =
      (state01, words00) := by
  decide +kernel

theorem prefix01 :
    trace directG1 1 40 36393 8800000000000000 19900 10 state00 =
      (state01, words00) := micro00

def state02 : KState := ⟨⟨362446354124204049, 362446359435038324⟩, ⟨769688205113557195, 769759755533525961⟩, true⟩

def words01 : List Nat := [371285022038265603, 371285018999222521, 371285015960227616, 371285015431960670, 371285013645469082, 371285011897293448, 371285010149092184, 371285008381646471, 371285003932259443, 371285001993047036]

set_option maxRecDepth 100000 in
theorem micro01 :
    trace directG1 1 40 36393 8800000000000000 19910 10 state01 =
      (state02, words01) := by
  decide +kernel

theorem prefix02 :
    trace directG1 1 40 36393 8800000000000000 19900 20 state00 =
      (state02, words00 ++ words01) := by
  rw [show 20 = 10 + 10 by decide, trace_append, prefix01]
  simp only [Nat.reduceAdd]
  rw [micro01]

def state03 : KState := ⟨⟨362428514437391776, 362428519753738190⟩, ⟨1125216943963745448, 1125288604214001678⟩, true⟩

def words02 : List Nat := [371285000053679574, 371284999414261526, 371284996682701927, 371284993653935318, 371284990625241166, 371284988331863575, 371284984893974728, 371284983964399127, 371284983034713289, 371284981801114708]

set_option maxRecDepth 100000 in
theorem micro02 :
    trace directG1 1 40 36393 8800000000000000 19920 10 state02 =
      (state03, words02) := by
  decide +kernel

theorem prefix03 :
    trace directG1 1 40 36393 8800000000000000 19900 30 state00 =
      (state03, words00 ++ words01 ++ words02) := by
  rw [show 30 = 20 + 10 by decide, trace_append, prefix02]
  simp only [Nat.reduceAdd]
  rw [micro02]

def state04 : KState := ⟨⟨362500474471748699, 362500479793676280⟩, ⟨(-309338489058769250), (-309266717547183608)⟩, true⟩

def words03 : List Nat := [371284978968659890, 371284977981136545, 371284978091377824, 371284978091996397, 371284975843422832, 371284973231082491, 371284970618733362, 371284970511693177, 371284969927514157, 371284970705990248]

set_option maxRecDepth 100000 in
theorem micro03 :
    trace directG1 1 40 36393 8800000000000000 19930 10 state03 =
      (state04, words03) := by
  decide +kernel

theorem prefix04 :
    trace directG1 1 40 36393 8800000000000000 19900 40 state00 =
      (state04, words00 ++ words01 ++ words02 ++ words03) := by
  rw [show 40 = 30 + 10 by decide, trace_append, prefix03]
  simp only [Nat.reduceAdd]
  rw [micro03]

def state05 : KState := ⟨⟨362436862081089993, 362436867408607690⟩, ⟨959158185892647335, 959230068899201397⟩, true⟩

def words04 : List Nat := [371284971037059595, 371284971037681343, 371284969158733777, 371284967353511075, 371284965548152803, 371284964515589582, 371284960140208670, 371284955631288395, 371284951122574994, 371284949116321936]

set_option maxRecDepth 100000 in
theorem micro04 :
    trace directG1 1 40 36393 8800000000000000 19940 10 state04 =
      (state05, words04) := by
  decide +kernel

theorem prefix05 :
    trace directG1 1 40 36393 8800000000000000 19900 50 state00 =
      (state05, words00 ++ words01 ++ words02 ++ words03 ++ words04) := by
  rw [show 50 = 40 + 10 by decide, trace_append, prefix04]
  simp only [Nat.reduceAdd]
  rw [micro04]

def state06 : KState := ⟨⟨362414378231148757, 362414383564239067⟩, ⟨1408059527809889475, 1408131522018958401⟩, true⟩

def words05 : List Nat := [371284946706752470, 371284946452386271, 371284946197833194, 371284945940601300, 371284943443561355, 371284941376767696, 371284939309875949, 371284938310317124, 371284934769612222, 371284931235682903]

set_option maxRecDepth 100000 in
theorem micro05 :
    trace directG1 1 40 36393 8800000000000000 19950 10 state05 =
      (state06, words05) := by
  decide +kernel

theorem prefix06 :
    trace directG1 1 40 36393 8800000000000000 19900 60 state00 =
      (state06, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05) := by
  rw [show 60 = 50 + 10 by decide, trace_append, prefix05]
  simp only [Nat.reduceAdd]
  rw [micro05]

def state07 : KState := ⟨⟨362458779388193807, 362458784726829479⟩, ⟨521809796702727450, 521881901624771770⟩, true⟩

def words06 : List Nat := [371284927701828025, 371284926667398482, 371284924613705066, 371284924836695925, 371284924837178270, 371284924303050815, 371284920851781384, 371284919294448987, 371284918021212407, 371284918021853254]

set_option maxRecDepth 100000 in
theorem micro06 :
    trace directG1 1 40 36393 8800000000000000 19960 10 state06 =
      (state07, words06) := by
  decide +kernel

theorem prefix07 :
    trace directG1 1 40 36393 8800000000000000 19900 70 state00 =
      (state07, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06) := by
  rw [show 70 = 60 + 10 by decide, trace_append, prefix06]
  simp only [Nat.reduceAdd]
  rw [micro06]

def state08 : KState := ⟨⟨362485668514822290, 362485673859102860⟩, ⟨(-15337551217265725), (-15265333538116165)⟩, true⟩

def words07 : List Nat := [371284916713766571, 371284914944685519, 371284913902268023, 371284913902950120, 371284913379365299, 371284912999318081, 371284912619090483, 371284912245930047, 371284909827628206, 371284909866633108]

set_option maxRecDepth 100000 in
theorem micro07 :
    trace directG1 1 40 36393 8800000000000000 19970 10 state07 =
      (state08, words07) := by
  decide +kernel

theorem prefix08 :
    trace directG1 1 40 36393 8800000000000000 19900 80 state00 =
      (state08, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07) := by
  rw [show 80 = 70 + 10 by decide, trace_append, prefix07]
  simp only [Nat.reduceAdd]
  rw [micro07]

def state09 : KState := ⟨⟨362403059947893082, 362403065297687829⟩, ⟨1635652456871009768, 1635724784752674716⟩, true⟩

def words08 : List Nat := [371284910858919481, 371284910859539283, 371284908896899533, 371284906941696667, 371284904986452488, 371284903075129058, 371284899913883852, 371284897433962458, 371284894954088966, 371284892450501870]

set_option maxRecDepth 100000 in
theorem micro08 :
    trace directG1 1 40 36393 8800000000000000 19980 10 state08 =
      (state09, words08) := by
  decide +kernel

theorem prefix09 :
    trace directG1 1 40 36393 8800000000000000 19900 90 state00 =
      (state09, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08) := by
  rw [show 90 = 80 + 10 by decide, trace_append, prefix08]
  simp only [Nat.reduceAdd]
  rw [micro08]

def state10 : KState := ⟨⟨362504014679867108, 362504020035284987⟩, ⟨(-382817072544680820), (-382744632229059980)⟩, true⟩

def words09 : List Nat := [371284888357723404, 371284886758770855, 371284886053072370, 371284886053695369, 371284884580343440, 371284882872242887, 371284881947729084, 371284881948422824, 371284882802967967, 371284883760487274]

set_option maxRecDepth 100000 in
theorem micro09 :
    trace directG1 1 40 36393 8800000000000000 19990 10 state09 =
      (state10, words09) := by
  decide +kernel

theorem prefix10 :
    trace directG1 1 40 36393 8800000000000000 19900 100 state00 =
      (state10, words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09) := by
  rw [show 100 = 90 + 10 by decide, trace_append, prefix09]
  simp only [Nat.reduceAdd]
  rw [micro09]

def words : List Nat := words00 ++ words01 ++ words02 ++ words03 ++ words04 ++ words05 ++ words06 ++ words07 ++ words08 ++ words09

theorem segment :
    trace directG1 1 40 36393 8800000000000000 19900 100 state00 =
      (state10, words) := by
  simpa only [words] using prefix10

end LeanCompCert.Ports.Section413WindowKGenerated.G1.Chunk199
