# 2022-09-26-M_square
증명을 코딩하기 발표자료

ocaml-system은 미리 설치해놓기.

```sh
opam switch create . ocaml-system --no-install
opam repo add coq-released https://coq.inria.fr/opam/released
opam pin add -n -y coq 8.15.0

make builddep
```