# Extra features

## En bref

- J'ai imlémenté un élaborateur (indépendant du type checker), dont je détaillerais le fonctionnement dans la partie suivante.

- En ce qui concerne la troisième idée d'amélioration (optimisation des programmes compilés), je n'ai rien implémenté de plus mais je vais tout de meme discuter ce point dans la denière partie.
  
## Elaboration

Mon élaborateur est intégralement implémenté dans le fichier `elaboration.ml`,
néanmoins il a également été nécessaire de modifier le fichier `source.ml` (afin d'ajouter un type pour les programmes avec annotations partielles de type) et `parser.ml` (afin de rendre facultatif les annotations de types dans la syntaxe, et de produire un programme à annotations partielles).
J'ai également modifié le fichier `options.ml` afin de pouvoir désactiver l'élaborateur si besoin (j'en ai besoin pour les tests de la task-2, qui sont censés tester le type-checker et non l'élaborateur, bien qu'il réussisse également les tests). J'ai d'ailleurs ajouté des tests pour l'élaborateur, ils sont situées dans `tests/elab` (ils fonctionnent de manière similaire aux tests de la task-2).

La structure globale de mon code concernant le typage est la suivante:  
Code source -Lexer/Parser-> `untyped_program` -Elaborateur-> `program_with_locations` -Typechecker-> `program_with_locations` (vérifié)  
avec `untyped_program` représentant les programmes avec annotations de type partielles (+ annotations de localisation).

Concernant l'implémentation:

- Pour l'unification, j'ai utilisé l'algorithme présenté dans les slides du cours sur l'inférence de type
- Pour l'élaboration, j'ai utilisé une version un peu simplifiée de l'algorithme W, lui aussi présenté dans les slides du cours. En effet, notre langage ne possédant pas de polymorphisme, les cas d'une variable et du `let` peuvent etre légeremment simplifiés. J'ai d'ailleurs été un peu surpris par le fait que l'absence de polymorphisme ne simplifie pas tellement les choses (un petit peu comme je l'ai dit, mais pour autant je n'ai pas trouvé d'algorithme plus simple que l'algorithme W).

Comportement: annotations de types prises en compte
Si pas de solution la plus général, erreur (lister les 3 erreurs)

## Optimisations

Je n'ai pas spécialement remarqué de lenteur excessive sur l'exemple donné en tache 5, et je n'ai pas trouvé de moyen simple et élégant de complexifier l'exemple.  
En effet, faire un réseau de neurone plus complexe aurait nécessité de prendre et manipuler beaucoup de poids en paramètre et aurait donc nécessité des extensions assez conséquentes pour faire cela proprement, notamment:
  - Extension de syntaxe sur les tuples (pour pouvoir les utiliser à la manière de tableaux à taille fixée à l'avance). Sinon, la déclaration du type et l'accès à un élément deviendrait trop laborieux quand le nombre de poids grossit.
  - Possibilité de parcourir ces memes tableaux sans avoir à répéter le code, via par exemple des sortes de boucles `for` à bornes fixées à l'avance (elles pourraient etre inlinés avant la compilation).

Je n'ai pas réalisé ces extensions de syntaxe, car je ne trouve pas cela très intéressant à implémenter (il s'agit surtout de tuyauterie...).

Concernant les optimisations, je n'ai pas su quoi faire pour la défonctorisation.
En effet, s'il s'agit d'éliminer les fonctions du premier ordre, je pense que mon `simplifier` le fait déjà, notamment grace aux règles suivantes:
  - Duplication: `(u Δ v) . w  -> (u . w) Δ (v . w)`
  - Elimination: `it . f -> it`
  - Application: `apply . ( ((curry f) . t1) Δ t2 ) -> f . (t1 Δ t2)` 
  - Quelques autres règles, notamment sur les paires.
  
En effet, ces règles semblent suffisantes à "béta-réduire" les termes autant que possible (cela termine toujours puisqu'il n'y a pas de récursion), et éliminent avec brio les fonctions du premier ordre de mon code. Dans le cas contraire, certains tests ne passeraient pas, car la façon dont je compile les `let` top-level fait que j'introduis des fonctions du premier ordre (et donc des `curry`, qu'il faut éliminer).

Plus généralement, sur les exemples donnés, le code produit en sortie du `simplifier` me semble bien souvent optimal (en tout cas, je ne vois pas comment je pourrais le simplifier plus). Je n'ai donc pas su implémenter d'optimisations additionnelles.