module spec

abstract sig Base {
  autor: one Usuario,
  likes: Int,
  dislikes: Int,
  conteudo: one Conteudo
}

sig Questao extends Base {
	respostas: set Resposta,
  titulo: one Titulo
}

sig Titulo{}

sig Conteudo{}

sig Resposta extends Base {
  comentarios: set Comentario
}

sig Usuario{}

sig Comentario extends Base {}

pred likesNaoNegativos[b:Base] {
  b.likes >= 0
}

pred dislikesNaoNegativos[b:Base] {
  b.dislikes >= 0
}


fact {
  all b:Base | dislikesNaoNegativos[b]
  all b:Base | likesNaoNegativos[b]
  all t:Titulo | one t.~titulo
  all c:Conteudo | one c.~conteudo
  all q1:Questao | all q2:Questao | (q1 != q2) implies (#(q1.respostas & q2.respostas) = 0)
  all r1:Resposta | all r2:Resposta | (r1 != r2) implies (#(r1.comentarios & r2.comentarios) = 0)
  all c:Comentario | one r:Resposta | c in r.comentarios
  all r:Resposta | one q:Questao | r in q.respostas
}

pred show[]{}
run show for 5