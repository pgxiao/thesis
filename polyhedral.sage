if '' not in sys.path:
    sys.path = [''] + sys.path
from igp import *
from sage.numerical.mip import MIPSolverException
from sage.misc.all import cached_method
from collections import defaultdict
from itertools import product

def construct_2d_strip_by_FastPiecewise(f):
    """
    （Credit by Shuidie Yao)
    Take a FastPiecewise function, convert it to straight 2d.
    Points are extended to lines, intervals are converted to rectangles
    
    EXAMPLES::
    
        sage: logging.disable(logging.INFO)
        sage: h = gmic()
        sage: for p in construct_2d_strip_by_FastPiecewise(h):
        ....:     p.vertices()
        (A vertex at (4/5, 0), A vertex at (4/5, 1))
        (A vertex at (1, 0),
         A vertex at (1, 1),
         A vertex at (4/5, 0),
         A vertex at (4/5, 1))
        (A vertex at (0, 0),
         A vertex at (0, 1),
         A vertex at (4/5, 0),
         A vertex at (4/5, 1))
        (A vertex at (0, 0), A vertex at (0, 1))
        (A vertex at (1, 0), A vertex at (1, 1))
    """
    polyhedra = set([Polyhedron(vertices = [[intv[0],0],[intv[1],0],[intv[0],1],[intv[1],1]]) for intv in f.intervals()])
    for intv in f.intervals():
        if len(intv) == 2:
            polyhedra.add(Polyhedron(vertices = [[intv[0],0],[intv[0],1]]))
            polyhedra.add(Polyhedron(vertices = [[intv[1],0],[intv[1],1]]))
        else:
            if intv[0] != intv[1] and intv.left_closed:
                polyhedra.add(Polyhedron(vertices = [[intv[0],0],[intv[0],1]]))
            if intv[0] != intv[1] and intv.right_closed:
                polyhedra.add(Polyhedron(vertices = [[intv[1],0],[intv[1],1]]))
    return polyhedra

def ideal_width(number_of_polyhedra, dim, constant=1, convergent_index=20):
    # FIXME: under experiment
    # Koeppe's comments on width:
    # 1) In the end, only computational experiment can determine what is the
    # most efficient choice of width.
    # 2) For small objects (like points), one would expect something like
    # constant * 1 / (number_of_polyhedra ^ (1 / dim)) (currently commented-out) 
    # to be best. Again, only computational experiments can determine what
    # constant to use.
    # 3) constant * 1 / (number_of_polyhedra ^ (1 / dim)) is irrational and
    # thus can't use it directly. So one needs to round it so that its
    # reciprocal is an integer.
    width = constant * 1 / (number_of_polyhedra ^ (1 / dim))
    cf = continued_fraction(1 / (number_of_polyhedra ^ (1 / dim)))
    cf_conv = cf.convergent(convergent_index)
    d = cf_conv.denominator()
    n = cf_conv.numerator()
    return 1 / ceil(d / n)

###############################
# Polyhedral Arrangement
###############################

class PolyhedralArrangement(object):
    """
    Define a Polyhedral Arrangement.

    INPUT:

    - ``collection`` -- either a list or a tuple or a set of polyhedra, 
    or a dictionary of polyhedra.
    The keys of the dictionary are the dimensions of the polyhedra

    Attributes:

    - ``ambient_dim`` -- the ambient dim of each polyhedron
        
    - ``dim`` -- the maximal dimension among the polyhedra
        
    - ``number_of_polyhedra`` -- the numbers of polyhedra (not including sub-polyhedra)
      when set up the arrangement
    
    - ``grid`` -- a :class:`Grid` that can be used for discrete binary search
      on polyhedra
        
    - ``collection`` -- a dictionary of the polyhedra (not including sub-polyhedra).
    The keys of the dictionary are the dimensions of the polyhedra
        
    - ``grid_contents`` -- a dictionary of the ``grid``, the keys are buckets
      and the values are a set of polyhedra that intersect with the key
        
    - ``polyhedron_buckets`` -- a dictionary. Each key is a polyhedron, and the value of
      the key is a list of buckets (each bucket is presented as a values set)
      that intersect with the polyhedron. This attribute is like an inverse of
      ``grid_contents``
 
    EXAMPLES::

        sage: p = Polyhedron(ieqs = [[0,1,0,0,0],[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1]], eqns = [[1,-1,-1,-1,-1]])
        sage: q = Polyhedron(eqns = [[10,30,50,60,70]])
        sage: collection = (p, q)
        sage: PA = PolyhedralArrangement(collection)
    """
    def __init__(self, collection, bucket_width=None):
        if isinstance(collection, (list, tuple, set)):
            coll_dict = {}
            for p in collection:
                d = p.dim()
                if d in coll_dict:
                    coll_dict[d].append(p)
                else:
                    coll_dict[d] = [p]
        elif isinstance(collection, dict):
            coll_dict = copy(collection)
        else:
            raise ValueError
        if not coll_dict:
            return
        self._ambient_dim = coll_dict.values()[0][0].ambient_dim()
        self._dim = max(coll_dict.keys())
        self._number_of_polyhedra = sum([len(v) for v in coll_dict.values()])
        self._grid = Grid(self._number_of_polyhedra, self._ambient_dim, bucket_width=bucket_width)
        self._collection = coll_dict
        self._grid_contents = self._grid._contents
        self._polyhedron_buckets = defaultdict(set)

    def __iter__(self):
        for polyhedron in self.collection_of_polyhedra():
            yield polyhedron

    def ambient_dimension(self):
        r"""
        The ambient dim of each polyhedron.
        """
        return self._ambient_dim

    def polyhedron_buckets(self):
        r"""
        A dictionary. Each key is a polyhedron, and the value of
        the key is a list of buckets (each bucket is presented
        as a values set) that intersect with the polyhedron.
        """
        self.update_dictionaries()
        return self._polyhedron_buckets

    def collection_of_polyhedra(self):
        r"""
        A list of polyhedra from the collection.
        """
        collection = set()
        coll_dict = self.collection_dict()
        for polyhedra_list in coll_dict.values():
            for polyhedron in polyhedra_list:
                collection.add(polyhedron)
        return list(collection)

    def collection_dict(self):
        r"""
        A dictionary of the polyhedra (not including sub-polyhedra).
        The keys of the dictionary are the dimensions of the polyhedra.
        """
        return self._collection

    def dim(self):
        r"""
        The maximal dimension among the polyhedra.
        """
        return self._dim

    def grid(self):
        r"""
        A :class:``Grid`` that can be used for discrete binary search
        on polyhedra.
        """
        return self._grid

    def grid_contents(self):
        r"""
        A dictionary of the ``grid``, the keys are buckets and the
        values are a set of polyhedra that intersect with the key.
        """
        self.update_dictionaries()
        return self._grid_contents

    def intersect(self, p, q):
        r"""
        Use binary search to check if two polyhedra ``p`` and ``q``
        intersect. Return True if they intersect, else return False.
        """
        p_buckets = self.in_buckets(p)
        q_buckets = self.in_buckets(q)
        if p_buckets.intersection(q_buckets) == set():
            return False
        if self.check_intersect_by_linear_programming(p, q):
            return True
        else:
            return False

    def in_buckets(self, p):
        r"""
        Return the sets of buckets that the polyhedron ``p`` locates
        in.

        EXAMPLES::

            sage: p = Polyhedron(vertices=[[8/21, 1/4], [4/5, 1/5], [5/6, 4/5]])
            sage: q = Polyhedron(vertices=[[1/2, 1/2], [5/6, 1/2], [1/2, 1]])
            sage: x = Polyhedron(vertices=[[4/5, 4/5]])
            sage: pa = PolyhedralArrangement([p, q, x])
            sage: pa.in_buckets(p)
            {(1, 0), (1, 1), (2, 0), (2, 1), (2, 2)}

            sage: poly = construct_2d_strip_by_FastPiecewise(h)
            sage: pa = PolyhedralArrangement(poly, bucket_width="ideal")
            sage: collection = pa.collection_of_polyhedra()
            sage: for p in collection:
            ....:         p.vertices()
            ....:         pa.in_buckets(p)
            (A vertex at (0, 0), A vertex at (0, 1))
            {(0, 0), (0, 1), (0, 2)}
            (A vertex at (0, 0),
             A vertex at (0, 1),
             A vertex at (4/5, 0),
             A vertex at (4/5, 1))
            {(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)}
            (A vertex at (1, 0),
             A vertex at (1, 1),
             A vertex at (4/5, 0),
             A vertex at (4/5, 1))
            {(2, 0), (2, 1), (2, 2)}
            (A vertex at (4/5, 0), A vertex at (4/5, 1))
            {(2, 0), (2, 1), (2, 2)}
            (A vertex at (1, 0), A vertex at (1, 1))
            {(2, 0), (2, 1), (2, 2)}
        """
        return self.polyhedron_buckets()[p]

    def construct_linear_programming_for_intersection(self, p, q):
        r"""
        Construct a LP to solve if polyhedron ``p`` and polyhedron ``q`` intersect

        EXAMPLES::

            sage: p = Polyhedron(ieqs = [[0,1,0,0,0],[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1]], eqns = [[1,-1,-1,-1,-1]])
            sage: q = Polyhedron(eqns = [[10,30,50,60,70]])
            sage: PA = PolyhedralArrangement((p, q))
            sage: lp = PA.construct_linear_programming_for_intersection(p, q)
            sage: lp.show()
            Maximization:
            <BLANKLINE>
            <BLANKLINE>
            Constraints:
              1.0 <= x_0 + x_1 + x_2 + x_3 <= 1.0
              -1.0 <= 3.0 x_0 + 5.0 x_1 + 6.0 x_2 + 7.0 x_3 <= -1.0
              - x_0 <= 0.0
              x_0 + x_1 + x_2 <= 1.0
              - x_2 <= 0.0
              - x_1 <= 0.0
            Variables:
              x_0 is a continuous variable (min=-oo, max=+oo)
              x_1 is a continuous variable (min=-oo, max=+oo)
              x_2 is a continuous variable (min=-oo, max=+oo)
              x_3 is a continuous variable (min=-oo, max=+oo)
            sage: # compare with the equations and inequalities from the polyhedra
            sage: p.equations(); q.equations(); p.inequalities(); q.inequalities()
            (An equation (1, 1, 1, 1) x - 1 == 0,)
            (An equation (3, 5, 6, 7) x + 1 == 0,)
            (An inequality (1, 0, 0, 0) x + 0 >= 0,
             An inequality (-1, -1, -1, 0) x + 1 >= 0,
             An inequality (0, 0, 1, 0) x + 0 >= 0,
             An inequality (0, 1, 0, 0) x + 0 >= 0)
            ()
        """
        if dim(p) == -1 or dim(q) == -1:
            raise ValueError("Cannot intersect with empty polyhedron")

        lp = MixedIntegerLinearProgram()
        x = lp.new_variable()
        lp.set_objective(0)

        def linear_constraint(cstr, cstr_type):
            """
            Construct linear constraint (can be equation or inequality depends
            on constraint type 'cstr_type') by the given constraint 'cstr'
            """
            s = sum(x[index] * coef for index, coef in enumerate(cstr[1:]))
            if cstr_type == "==":
                return s == -cstr[0]
            else:
                return s >= -cstr[0]

        eqns = p.equations_list() + q.equations_list()
        ieqs = p.inequalities_list() + q.inequalities_list()
        # FIXME: (suggestion by Yuan) might use to_linear_program create LPs and inequalities
        for eqn in eqns:
            f = linear_constraint(eqn, "==")
            lp.add_constraint(f)
        for ieq in ieqs:
            g = linear_constraint(ieq, ">=")
            lp.add_constraint(g)
        return lp

    def check_intersect_by_linear_programming(self, p, q):
        r"""
        Use LP to check if two polyhedra intersect.
        Return True if polyhedron ``p`` and polyhedron ``q`` intersect.
        Return False it they do not intersect.

        EXAMPLES::

            sage: p = Polyhedron(ieqs = [[0,1,0,0,0],[0,0,1,0,0],[0,0,0,1,0],[0,0,0,0,1]], eqns = [[1,-1,-1,-1,-1]])
            sage: q = Polyhedron(eqns = [[10,30,50,60,70]])
            sage: PA = PolyhedralArrangement((p, q))
            sage: PA.check_intersect_by_linear_programming(p, q)
            False
            sage: p.intersection(q)
            The empty polyhedron in QQ^4

            sage: cube = polytopes.hypercube(3)
            sage: oct = polytopes.cross_polytope(3)
            sage: PA.check_intersect_by_linear_programming(cube, oct)
            True
            sage: cube.intersection(oct*2)
            A 3-dimensional polyhedron in ZZ^3 defined as the convex hull of 12 vertices

            sage: P = Polyhedron([(0,0),(1,1)], base_ring=ZZ)
            sage: PA.check_intersect_by_linear_programming(P, P)
            True
            sage: P.intersection(P)
            A 1-dimensional polyhedron in ZZ^2 defined as the convex hull of 2 vertices

            sage: Q = Polyhedron([(0,1),(1,0)], base_ring=ZZ)
            sage: PA.check_intersect_by_linear_programming(P, P)
            True
        """
        lp = self.construct_linear_programming_for_intersection(p, q)
        try:
            lp.solve()
            return True
        except MIPSolverException:
            return False
        else:
            print "Unexpected error"
            raise

    def point_lookup(self, point):
        r"""
        Given a point, find where the bucket that the point belong to,
        and return the contents on that bucket as a set.

        EXAMPLES::

            sage: p = Polyhedron(vertices=[[8/21, 1/4], [4/5, 1/5], [5/6, 4/5]])
            sage: q = Polyhedron(vertices=[[1/2, 1/2], [5/6, 1/2], [1/2, 1]])
            sage: x = Polyhedron(vertices=[[4/5, 4/5]])
            sage: pa = PolyhedralArrangement([p, q, x])
            sage: pa.point_lookup(x)
            {A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices,
             A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices,
             A 0-dimensional polyhedron in QQ^2 defined as the convex hull of 1 vertex}
        """
        self.update_dictionaries()
        point = point.vertices_list()[0]
        bucket = self.grid().point_in_bucket(point)
        return self.grid_contents()[bucket]

    def point_in_polyhedra(self, point):
        r"""
        (Required by Shuidie)
        Find which polyhedra the point locates on.
        Return a list of those polyhedra.

        EXAMPLES::

            sage: h1 = gmic()
            INFO: 2017-03-08 15:54:49,336 Rational case.
            sage: poly = construct_2d_strip_by_FastPiecewise(h1)
            sage: pa = PolyhedralArrangement(poly, bucket_width="ideal")
            sage: point = (4/5, 1)
            sage: intersect_poly = pa.point_in_polyhedra(point)
            sage: for p in intersect_poly:
            ....:         p.vertices()
            (A vertex at (1, 0),
             A vertex at (1, 1),
             A vertex at (4/5, 0),
             A vertex at (4/5, 1))
            (A vertex at (0, 0),
             A vertex at (0, 1),
             A vertex at (4/5, 0),
             A vertex at (4/5, 1))
            (A vertex at (4/5, 0), A vertex at (4/5, 1))
            sage: h2 = rlm_dpl1_extreme_3a()
            INFO: 2017-03-08 15:57:04,237 Rational case.
            sage: poly = construct_2d_strip_by_FastPiecewise(h2)
            sage: pa = PolyhedralArrangement(poly, bucket_width="ideal")
            sage: point = (5/8, 1/2)
            sage: intersect_poly = pa.point_in_polyhedra(point)
            sage: for p in intersect_poly:
            ....:         p.vertices()
            (A vertex at (1, 0),
             A vertex at (1, 1),
             A vertex at (5/8, 0),
             A vertex at (5/8, 1))
            (A vertex at (1/4, 0),
             A vertex at (1/4, 1),
             A vertex at (5/8, 0),
             A vertex at (5/8, 1))
            (A vertex at (5/8, 0), A vertex at (5/8, 1))
        """
        possible_intersect = self.point_lookup(Polyhedron(vertices=[point]))
        return [p for p in possible_intersect if p.contains(point)]

    def number_of_polyhedra(self):
        r"""
        Return the numbers of polyhedra of arrangement.
        """
        return self._number_of_polyhedra

    @cached_method
    def update_dictionaries_for_a_polyhedron(self, p, selection=None):
        r"""
        Use binary search to find what buckets the polyhedron ``p``
        located in and update two dictionaries: ``grid_contents`` and
        ``buckets``.

        Recall:

        - ``grid_contents`` -- a dictionary of the ``grid``, the keys are buckets
          and the values are a set of polyhedra that intersect with the key
            
        - ``buckets`` -- a dictionary, the keys are polyhedra and the values are the
          buckets that intersect with the key (this attribute is like a dual
          of ``grid_contents``)

        INPUT:

        - ``p`` -- a :class:`Polyhedron`

        - ``selection`` -- (default: None) a tuple of two buckets
          (buckets are represented by its integer coordinates,
          see :class:`Grid` for examples)
          if ``selection`` is None, then choose the entire grid as
          selection

        EXAMPLES::

            sage: p = Polyhedron(vertices=[[8/21, 1/4], [4/5, 1/5], [5/6, 4/5]])
            sage: q = Polyhedron(vertices=[[1/2, 1/2], [4/5, 1/2], [1/2, 5/6]])
            sage: x = Polyhedron(vertices=[[4/5, 4/5]])
            sage: pa = PolyhedralArrangement([p, q, x])
            sage: pa.update_dictionaries_for_a_polyhedron(p)
            sage: pa.grid_contents()
            defaultdict(<type 'set'>, {(2, 0): set([A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices]), (1, 0): set([A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices]), (1, 1): set([A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices]), (2, 1): set([A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices]), (2, 2): set([A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices])})
            sage: pa.polyhedron_buckets()
            defaultdict(<type 'set'>, {A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices: set([(2, 0), (1, 0), (1, 1), (2, 1), (2, 2)])})
        """
        grid = self.grid()
        if selection is None:
            size = grid.size()
            dim = grid.dim()
            selection = (tuple(0 for i in range(dim)), tuple(size - 1 for i in range(dim)))
        lower_left, upper_right = selection
        if self.check_intersect_by_linear_programming(grid.selection_to_polyhedron(lower_left, upper_right), p):
            if lower_left == upper_right:
                grid._contents[lower_left].add(p)
                self._polyhedron_buckets[p].add(lower_left)
            else:
                a, b = grid.cut_selection(lower_left, upper_right)
                self.update_dictionaries_for_a_polyhedron(p, a)
                self.update_dictionaries_for_a_polyhedron(p, b)

    @cached_method
    def update_dictionaries(self, selection=None):
        r"""
        For each polyhedron in the collection, use binary search to 
        find what buckets the polyhedron located in and update two
        dictionaries: ``bucket`` and ``grid_contents``.

        See :meth:`update_dictionaries_for_a_polyhedron` for more
        docstrings.

        EXAMPLES::

            sage: p = Polyhedron(vertices=[[8/21, 1/4], [4/5, 1/5], [5/6, 4/5]])
            sage: q = Polyhedron(vertices=[[1/2, 1/2], [5/6, 1/2], [1/2, 1]])
            sage: x = Polyhedron(vertices=[[4/5, 4/5]])
            sage: pa = PolyhedralArrangement([p, q, x])
            sage: pa.update_dictionaries()
            sage: pa.grid_contents()
            defaultdict(<type 'set'>, {(1, 2): set([A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices]), (2, 1): set([A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices, A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices]), (2, 0): set([A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices]), (2, 2): set([A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices, A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices, A 0-dimensional polyhedron in QQ^2 defined as the convex hull of 1 vertex]), (1, 0): set([A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices]), (1, 1): set([A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices, A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices])})
            sage: pa.polyhedron_buckets()
            defaultdict(<type 'set'>, {A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices: set([(2, 0), (1, 0), (1, 1), (2, 1), (2, 2)]), A 2-dimensional polyhedron in QQ^2 defined as the convex hull of 3 vertices: set([(1, 2), (1, 1), (2, 1), (2, 2)]), A 0-dimensional polyhedron in QQ^2 defined as the convex hull of 1 vertex: set([(2, 2)])})
        """
        for p in self.collection_of_polyhedra():
            self.update_dictionaries_for_a_polyhedron(p, selection)

class Grid(object):
    r"""
    Define a grid that are divided into buckets. The grid
    will be used for discrete binary search to find polyhedra
    intersection in :class:`PolyhedralArrangement`.

    # definition of terms:
    # 1. bucket - a single bucket in the grid with integer coordinates.
    # 2. selection - a bounch of buckets which can be determined by 
    #    the lower left bucket and upper right bucket.
    #    Think of a cube that can be determined by the lower left vertex
    #    and upper right vertex.

    INPUT:

    - ``number_of_polyhedra`` -- an integer, the number of polyhedra
      in the collection in a :class:`PolyhedralArrangement`

    - ``dim`` -- the dimension of the grid

    - ``bucket_width`` -- the width of the bucket

    Attributes:

    - ``bucket_width`` -- the width of each bucket

    - ``size`` -- an integer that indicates how many pieces
      are divided from 0 to 1

    - ``dim`` -- an integer that indicates the dimension
      of the grid

    - ``buckets`` -- a set that includes all the buckets
      in the grid

    - ``contents`` -- a dictionary, the keys are buckets
      and the values are the contents on the buckets. In
      this codes (so far), the contents are sets of polyhedra
      that intersect with the keys
    """ 
    def __init__(self, number_of_polyhedra, dim, bucket_width=None):
        # size is the number of polyhedra
        # dim is the ambient dimension of the polyhedra
        # FIXME: width can only be fractional
        if bucket_width is None:
            # self._bucket_width = 1 / (number_of_polyhedra ^ (1 / dim))
            self._bucket_width = 1 / number_of_polyhedra
        elif bucket_width == "ideal":
            self._bucket_width = ideal_width(number_of_polyhedra, dim)
        else:
            print "Unknown bucket_width option"
        self._size = Integer(1 / self._bucket_width)
        self._dim = dim
        self._contents = defaultdict(set)

    @cached_method
    def all_buckets(self):
        r"""
        Return a set that includes all the buckets in the grid


        EXAMPLES::

            sage: g = Grid(3, 2)
            sage: g.all_buckets()
            {(0, 0), (0, 1), (0, 2), (1, 0), (1, 1), (1, 2), (2, 0), (2, 1), (2, 2)}
        """
        return set(product(range(self._size), repeat=self._dim))

    @cached_method
    def bucket_to_hypercube(self, lower_left):
        r"""
        Return a hypercube in standard width by giving the coordinates
        of the lower left bucket.

        EXAMPLES::

            sage: g = Grid(3, 3)
            sage: g.bucket_to_hypercube((0, 0, 0)).vertices()
            (A vertex at (0, 0, 0),
             A vertex at (0, 0, 1/3),
             A vertex at (0, 1/3, 0),
             A vertex at (0, 1/3, 1/3),
             A vertex at (1/3, 0, 0),
             A vertex at (1/3, 0, 1/3),
             A vertex at (1/3, 1/3, 0),
             A vertex at (1/3, 1/3, 1/3))
        """
        origin = self.real_coordinate(lower_left)
        unit_grid_iter = product([0, self.bucket_width()], repeat=self.dim())
        unit_grid = [list(v) for v in unit_grid_iter]
        v_list = [0] * len(unit_grid)
        for index, v in enumerate(unit_grid):
            v_list[index] = [o + p for o, p in zip(v, origin)]
        return Polyhedron(vertices=v_list)

    def change_coordinate(self, bucket, index, offset):
        r"""
        Change one coordinate of the given bucket.

        EXAMPLES::

            sage: g = Grid(3, 3)
            sage: g.change_coordinate((0, 1, 2), 2, -1)
            (0, 1, 1)
        """
        return bucket[:index] + (bucket[index] + offset,) + bucket[1 + index:]

    def contents(self):
        r"""
        A dictionary, the keys are buckets and the values are the contents
        on the buckets. In this codes (so far), the contents are sets of
        polyhedra that intersect with the keys.
        """
        return self._contents

    def cut_selection(self, lower_left, upper_right):
        r"""
        Given the lower left bucket and upper right bucket of the selection,
        find the 'longest' edges, and cut it into two new selections.

        If all edges are equal, cut the selection from its first coordinate.

        Return two selections with their lower left and upper right buckets.

        EXAMPLES::

            sage: g = Grid(3, 3)
            sage: g.cut_selection((0, 0, 0), (2, 2, 2))
            (((0, 0, 0), (0, 2, 2)), ((1, 0, 0), (2, 2, 2)))
            sage: g.cut_selection((1, 1, 1), (1, 1, 1))
            ((1, 1, 1), (1, 1, 1))
        """
        if lower_left == upper_right:
            return lower_left, lower_left
        index, length = self.longest_edge_of_selection(lower_left, upper_right)
        lower_left_offset = length // 2
        # cut the selection into two new selection
        # assume the lower left selection is smaller if length is odd
        small = (lower_left, self.change_coordinate(upper_right, index, -(length - lower_left_offset)))
        large = (self.change_coordinate(lower_left, index, lower_left_offset), upper_right)
        return small, large

    def dim(self):
        r"""
        Return the dimension of the grid.
        """
        return self._dim

    def edges_of_selection(self, lower_left, upper_right):
        r"""
        Return the lengths of the edges of the selection.

        EXAMPLES::

            sage: g = Grid(3, 3)
            sage: g.edges_of_selection((0, 1, 1), (1, 2, 1))
            [2, 2, 1]
        """
        return [c1 - c0 + 1 for c0, c1 in zip(lower_left, upper_right)]

    def real_coordinate(self, bucket):
        r"""
        Get the actual coordinate of the bucket.

        EXAMPLES::

            sage: g = Grid(3, 3)
            sage: g.real_coordinate((0, 1, 2))
            (0, 1/3, 2/3)
        """
        return tuple(coord * self.bucket_width() for coord in bucket)

    def longest_edge_of_selection(self, lower_left, upper_right):
        r"""
        Find the longest edge of a selection.

        EXAMPLES::

            sage: g = Grid(3, 3)
            sage: g.longest_edge_of_selection((0, 1, 1), (1, 2, 1))
            (0, 2)
        """
        edges = self.edges_of_selection(lower_left, upper_right)
        maximal_edge = max(edges)
        index = edges.index(maximal_edge)
        return index, maximal_edge

    def selection_to_polyhedron(self, lower_left, upper_right):
        r'''
        Convert a selection to a polyhedron.

        EXAMPLES::

            sage: g = Grid(3, 3)
            sage: # build a flat box 
            sage: # (i.e. the height is half of the width or of the length)
            sage: p = g.selection_to_polyhedron((1, 1, 2), (2, 2, 2))
            sage: p.vertices()
            (A vertex at (1, 1, 1),
             A vertex at (1/3, 1/3, 2/3),
             A vertex at (1/3, 1/3, 1),
             A vertex at (1/3, 1, 2/3),
             A vertex at (1/3, 1, 1),
             A vertex at (1, 1/3, 2/3),
             A vertex at (1, 1/3, 1),
             A vertex at (1, 1, 2/3))
        '''
        if lower_left == upper_right:
            return self.bucket_to_hypercube(lower_left)
        edges = self.edges_of_selection(lower_left, upper_right)
        # note: upper_right is the bucket that is hased with
        # the actual lower left vertex of the bucket
        # therefore, to get the actual upper right vertex of the selection
        # all coordinates of the upper right bucket needed to add one
        new_upper_right = tuple(c + 1 for c in upper_right)
        vertices_set = set([lower_left, new_upper_right])
        for i in range(self.dim()):
            up = self.change_coordinate(lower_left, i, edges[i])
            down = self.change_coordinate(new_upper_right, i, -edges[i])
            vertices_set.add(up)
            vertices_set.add(down)
        real_vertices = [self.real_coordinate(p) for p in list(vertices_set)]
        return Polyhedron(vertices=real_vertices)

    def point_in_bucket(self, point):
        r"""
        Return a bucket where the point are located in.

        EXAMPLES:

            sage: g = Grid(3, 3)
            sage: g.point_in_bucket((1/4, 1/2, 1))
            (0, 1, 2)
        """
        return tuple(((p) // (self._bucket_width)).floor() if p != 1
                    else self._size - 1
                    for p in point)

    def bucket_width(self):
        r"""
        Return the width of the grid.

        EXAMPLES::

            sage: g = Grid(2, 3)
            sage: g.bucket_width()
            1/2
        """
        return self._bucket_width

    def size(self):
        r"""
        Return the size of the grid.

        EXAMPLES::

            sage: g = Grid(2, 3)
            sage: g.size()
            2
        """
        return self._size
