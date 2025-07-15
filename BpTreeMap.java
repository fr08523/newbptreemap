
/************************************************************************************
 * @file BpTreeMap.java
 *
 * @author  John Miller
 *
 * Split Nodes on Overflow
 *    Divider Key (DK) splits the left subtree (all keys < DK)
 *                        and the right subtree (all keys >= DK)
 *    Without deletions DK = smallest key in right subtree (SMALLEST RIGHT RULE)
 *    Note: DK is a middle key
 *    Cases: for tree order (fanout) p >= 3: evens and odds
 *
 *-----------------------------------------------------------------------------------
 * A. Leaf Node Split Rule:
 *    Split node into (node, rsib) with floor(p/2), ceil(p/2) keys, respectively
 *    Divider Key (DK) Copied Up
 *
 * Structure for order = p = 4 (max of 3 keys), upon first split
 *     [[ . k0 . k1 . k2 . k3 . ]] <- node OVERFLOW -> Split
 * [ . k2 . -- . -- . -- . ]       <- parent DK = k2
 *     [ . k0 . k1 . -- . ]        <- node
 *     [ . k2 . k3 . -- . ]        <- rsib
 *
 * Structure for order = 5 (max of 4 keys), upon first split
 *     [[ . k0 . k1 . k2 . k3 . k4 .]] <- node OVERFLOW -> Split
 * [ . k2 . -- . -- . -- . ]           <- parent DK = k2
 *     [ . k0 . k1 . -- . -- . ]       <- node
 *     [ . k2 . k3 . k4 . -- . ]       <- rsib
 *
 *-----------------------------------------------------------------------------------
 * B. Internal Node Split Rule:
 *    Split node into (node, rsib) with floor((p-1)/2), ceil((p-1)/2) keys, respectively
 *    Divider Key (DK) Promoted Up
 *
 * Structure for order = p = 4 (max of 3 keys), upon first split
 *     [[ . k0 . k1 . k2 . k3 . ]] <- node OVERFLOW -> Split
 * [ . k1 . -- . -- . -- . ]       <- parent DK = k1
 *     [ . k0 . -- . -- . ]        <- node
 *     [ . k2 . k3 . -- . ]        <- rsib
 *
 * Structure for order = 5 (max of 4 keys), upon first split
 *     [[ . k0 . k1 . k2 . k3 . k4 .]] <- node OVERFLOW -> Split
 * [ . k2 . -- . -- . -- . ]           <- parent DK = k2
 *     [ . k0 . k1 . -- . -- . ]       <- node
 *     [ . k3 . k4 . -- . -- . ]       <- rsib
 */

// U N D E R   D E V E L O P M E N T

import java.io.*;
import java.lang.reflect.Array;
import java.util.*;

import static java.lang.Math.ceilDiv;
import static java.lang.System.out;

/************************************************************************************
 * The `BpTreeMap` class provides B+Tree maps.  B+Trees are used as multi-level index
 * structures that provide efficient access for both point queries and range queries.
 * All keys will be at the leaf level with leaf nodes linked by references.
 * Internal nodes will contain Divider Keys (DKs) such that each divider key corresponds to
 * the smallest key in its right subtree (SMALLEST RIGHT).  Keys in left subtree are "<",
 * while keys in right subtree are ">=".
 */
public class BpTreeMap <K extends Comparable <K>, V>
       extends AbstractMap <K, V>
       implements Serializable, Cloneable // , SortedMap <K, V>       // FIX -- use SortedMap
{
    private static final boolean DEBUG = true;                        // debug flag

    private static final int ORDER = 5;                               // (p) maximum number of children for a B+Tree node.

//  Split leaf node into (node, rsib) with floor(p/2), ceil(p/2) keys, respectively
    private static final int LHALF  = ORDER / 2;                      // left-half of max keys (floor)
    private static final int RHALF  = ceilDiv (ORDER, 2);             // right-half of max keys (ceil)

//  Split internal node into (node, rsib) with floor((p-1)/2), ceil((p-1)/2) keys, respectively
    private static final int LiHALF = (ORDER - 1) / 2;                // left-internal-half of max keys (floor)
    private static final int RiHALF = ceilDiv ((ORDER - 1), 2);       // right-internal-half of max keys (ceil)

    private final Class <K> classK;                                   // The class for type K (key).
    private final Class <V> classV;                                   // The class for type V (value).

//-----------------------------------------------------------------------------------
// Node inner class
//-----------------------------------------------------------------------------------

    /********************************************************************************
     * The `Node` inner class defines nodes that are stored in the B+tree map.
     * Node key: [ . k0 . k1 . k2 . k3 . ]
     *              <  <=   <=   <=   <=         note: number of keys is one less than number of refs
     *      ref:  r0   r1   r2   r3   r4
     * Leaf:      r0 -> next leaf node; r1 -> tuple (k0, ...); r2 -> tuple (k1, ...); etc.
     * Internal:  r0 -> subtree with keys < k0; r1 -> subtree with keys in [k0, k1); etc.
     * Split:     extra room in nodes allows the overflow key to be inserted before split
     */
    private class Node
    {
        boolean   isLeaf;                                             // whether the node is a leaf 
        int       keys;                                               // number of active keys
        K []      key;                                                // array of keys
        Object [] ref;                                                // array of references/pointers

        /****************************************************************************
         * Construct a BpTree node containing keys_ keys.
         * @param keys_    number of initial keys
         * @param isLeaf_  whether the node is a leaf
         */
        @SuppressWarnings("unchecked")
        Node (int keys_, boolean isLeaf_)
        {
            isLeaf = isLeaf_;
            keys   = keys_;
            key    = (K []) Array.newInstance (classK, ORDER);
            ref = (isLeaf) ? new Object [ORDER + 1]
                           : (Node []) Array.newInstance (Node.class, ORDER + 1);
        } // constructor

        /****************************************************************************
         * Construct a new root node with one key (and two references) in it.
         * @param left   the left node (< dkey)
         * @param dkey   the divider key
         * @param right  the right node (>= dkey)
         */
        Node (Node left, K dkey, Node right)
        {
            this (1, false);
            key[0] = dkey;                                            // divider key
            ref[0] = left; ref[1] = right;                            // left and right references
        } // constructor

        /****************************************************************************
         * Return whether this node has overflowed (too many keys).
         */
        boolean overflow () { return keys >= ORDER; }

        /****************************************************************************
         * Find and return the first position where 'k < key_i' in this node.
         * @param k  the key whose position is sought
         */
        int find (K k)
        {
            for (var i = 0; i < keys; i++) if (k.compareTo (key[i]) < 0) return i;
            return keys;
        } // find

        /****************************************************************************
         * Find and return the first position where 'k == key_i' in this node.
         * @param k  the key whose position is sought
         */
        int findEq (K k)
        {
            for (var i = 0; i < keys; i++) if (k.compareTo (key[i]) == 0) return i;
            return -1;
        } // find

        /****************************************************************************
         * Add the new key k and value v into this node at insertion position (ip).
         * @param k  the new key
         * @param v  the new value (or node for internal nodes)
         */
        void add (K k, Object v)
        {
            var ip = find (k);                                          // find insertion position (ip)
            for (var i = keys; i > ip; i--) {                           // make room by shifting keys right
                key[i]   = key[i-1];
                ref[i+1] = ref[i];
            } // for
            key[ip]   = k;                                              // insert new key
            ref[ip+1] = v;                                              // insert new value (right of key)
            keys     += 1;                                              // increment to number of active keys
        } // add

        /****************************************************************************
         * Split this LEAF node by creating a right sibling node (rt) and moving the
         * RHALF largest keys with their references to that new node, leaving LHALF.
         * Return the right sibling node, where the divider key is key[0].
         */
        Node split ()
        {
            var rt = new Node (RHALF, true);                            // allocate leaf right sibling node (rt)
            for (var i = 0; i < RHALF; i++) {                           // move largest half of keys (with refs) to rt
                rt.key[i]   = key[LHALF + i];
                rt.ref[i+1] = ref[LHALF + i+1];                         // refs are right of keys
            } // for
            rt.ref[0] = ref[0];                                         // update LINKED LIST of nodes
            ref[0]    = rt;                                             // this -> rt -> old-right
            keys      = LHALF;                                          // reset number of active keys to LHALF
            return rt;                                                  // (divider key (smallest right) in right sibling
        } // split

        /****************************************************************************
         * Split this INTERNAL node by creating a right sibling node (rt) and moving the
         * RiHALF largest keys with their references to that new node, leaving LiHALF.
         * Return the right sibling node, where the divider key is key[0].
         */
        Node splitI ()
        {
            var rt = new Node (RiHALF, false);                          // allocate internal right sibling node (rt)
            for (var i = 0; i < RiHALF; i++) {                          // move largest half of keys (with refs) to rt
                rt.key[i] = key[LiHALF + i];
                rt.ref[i] = ref[LiHALF + i];
            } // for
            rt.ref[RiHALF] = ref[keys];                                 // copy over the last ref
            keys = LiHALF;                                             // reset number of active keys to LiHALF
            return rt;                                                  // divider key (middle key) in right sibling
        } // splitI

        /****************************************************************************
         * Convert this node to a string.
         */
        @Override
        public String toString ()
        {
            var sb = new StringBuilder ("[ . " );
            for (var i = 0; i < keys; i++) sb.append (key[i] + " . ");
            sb.append ("]");
            return sb.toString ();
        } // toString

        /****************************************************************************
         * Show the node's data structure.
         */
        void show ()
        {
            out.println ("isLeaf = " + isLeaf);
            out.println ("keys   = " + keys);
            out.println ("key    = " + Arrays.deepToString (key));
            out.println ("ref    = " + Arrays.deepToString (ref));
        } // show

        /****************************************************************************
         * Show the node's references.
         */
        void showRef ()
        {
            out.println ("ref = " + Arrays.deepToString (ref));
        } // showRef

    } // Node

//-----------------------------------------------------------------------------------
// Fields and constructors for B+Tree class
//-----------------------------------------------------------------------------------

    private Node root;                                                // root of the B+Tree
    private final Node firstLeaf;                                     // first (leftmost) leaf in the B+Tree

    private int count  = 0;                                           // counter for number nodes accessed (for performance testing)
    private int kCount = 0;                                           // counter for total number of keys in the B+Tree Map

    /********************************************************************************
     * Construct an empty B+Tree map.
     * @param _classK  the class for keys (K)
     * @param _classV  the class for values (V)
     */
    public BpTreeMap (Class <K> _classK, Class <V> _classV)
    {
        classK    = _classK;
        classV    = _classV;
        root      = new Node (0, true);                                // make an empty root
        firstLeaf = root;
    } // constructor

    /********************************************************************************
     * Return null to use the natural order based on the key type.  This requires the
     * key type to implement Comparable.
    public Comparator <? super K> comparator () 
    {
        return null;
    } // comparator
     */

    /********************************************************************************
     * Return the size (number of keys) in the B+Tree.
     * @return  the size of the B+Tree
     */
    public int size () { return kCount; }

//-----------------------------------------------------------------------------------
// Retrieve values or ranges (subtrees)
//-----------------------------------------------------------------------------------

    /********************************************************************************
     * Return a set containing all the entries as pairs of keys and values.
     * @return  the set view of the map
     */
    public Set <Map.Entry <K, V>> entrySet ()
    {
        var enSet = new HashSet <Map.Entry <K, V>> ();

        //  T O   B E   I M P L E M E N T E D
            
        return enSet;
    } // entrySet

    /********************************************************************************
     * Given the key, look up the value in the B+Tree map.
     * @param key  the key used for look up
     * @return  the value associated with the key or null if not found
     */
    @SuppressWarnings("unchecked")
    public V get (Object key) { return find ((K) key); }

    record NodePos (Object node, int pos) {}                          // as records are implicitly static, can't use 'Node node'

    /********************************************************************************
     * Find the given key in this B+tree and return its corresponding value.
     * Calls the recursive findp method.
     * @param key  the key to find
     */
    @SuppressWarnings("unchecked")
    public V find (K key)
    {
        var np = findp (key, root);                                   // leaf node, index position
        return (np.pos >= 0) ? (V) ((Node) np.node).ref[np.pos+1]
                             : (V) null;
    } // find

    /********************************************************************************
     * Recursive helper method for finding the position of the given key in this B+tree.
     * @param key  the key to find
     * @param n    the current node
     */
    @SuppressWarnings("unchecked")
    private NodePos findp (K key, Node n)
    {
        count += 1;
        return (n.isLeaf) ? new NodePos (n, n.findEq (key))
                          : findp (key, (Node) n.ref[n.find (key)]);
    } // findp

//-----------------------------------------------------------------------------------
// Put key-value pairs into the B+Tree
//-----------------------------------------------------------------------------------

    /********************************************************************************
     * Put the key-value pair in the B+Tree map.
     * @param key    the key to insert
     * @param value  the value to insert
     * @return  null, not the previous value for this key
     */
    public V put (K key, V value)
    {
        kCount += 1;
        insert (key, value, root);
        return null;
    } // put

    /********************************************************************************
     * Recursive helper function for inserting a key into a B+tree.
     * Add key-ref pair into node n and when it is full, split node n by allocating
     * a right sibling node rt and placing half of n's key in rt.
     * A split also will require a key-ref pair to be inserted at the next level up.
     * @param key  the key to insert
     * @param ref  the value/node to insert
     * @param n    the current node
     * @return  the newly allocated right sibling node of n 
     */
    @SuppressWarnings("unchecked")
    private Node insert (K key, V ref, Node n)
    {
        out.println ("=============================================================");
        out.println ("insert: key " + key);
        out.println ("=============================================================");

        Node rt = null;                                               // holder right sibling node

        if (n.isLeaf) {                                               // handle LEAF node level
            rt = add (n, key, ref);
            if (rt != null) {
                if (n != root) return rt;
                root = new Node (root, rt.key[0], rt);                // make a new root
            } // if

        } else {                                                      // handle INTERNAL node level
            rt = insert (key, ref, (Node) n.ref[n.find (key)]);       // recursive call to insert
            if (DEBUG) out.println ("insert: handle internal node level");

            if (rt != null) {                                        // child split -> add to this node
                var rrt = addI (n, rt.key[0], rt);                    // insert divider key
                if (rrt != null) {                                    // this node also split
                    if (n != root) return rrt;
                    root = new Node (root, rrt.key[0], rrt);          // create new root
                } // if
            } // if

        } // if

        if (DEBUG) printT (root, 0);
        return rt;                                                    // return right sibling node
    } // insert

    /********************************************************************************
     * Add new key k and value v into LEAF node n.  Upon overflow, split node n,
     * in which case the new right sibling node (containing the divider key) is returned.
     * @param n  the current node
     * @param k  the new key
     * @param v  the new value
     */
    private Node add (Node n, K k, V v)
    {
        Node rt = null;                                               // holder for right sibling rt
        n.add (k, v);                                                 // add into node n
        if (n.overflow ()) rt = n.split ();                           // full => split into n and rt, divider key is rt.key[0]
        return rt;
    } // add

    /********************************************************************************
     * Add new key k and value v into INTERNAL node n.  Upon overflow, split node n,
     * in which case the new right sibling node (containing the divider key) is returned.
     * @param n  the current node
     * @param k  the new key
     * @param v  the new left value (ref a node)
     */
    private Node addI (Node n, K k, Node v)
    {
        Node rt = null;                                               // holder for right sibling rt

        n.add (k, v);                                                 // add into internal node
        if (n.overflow ()) rt = n.splitI ();                          // full => split node
        return rt;
    } // addI

    /**********************************************************************
     * Delete the given key from this B+Tree map.  Only handles removal from
     * a leaf node without re-balancing.
     * @param k  the key to delete
     * @return the value associated with the deleted key or null
     */
    @SuppressWarnings("unchecked")
    public V delete (K k)
    {
        var np = findp (k, root);
        if (np.pos < 0) return null;                                  // not found

        var n = (Node) np.node;
        V old = (V) n.ref[np.pos + 1];
        for (int i = np.pos; i < n.keys - 1; i++) {
            n.key[i]   = n.key[i+1];
            n.ref[i+1] = n.ref[i+2];
        }
        n.key[n.keys - 1] = null;
        n.ref[n.keys] = null;
        n.keys -= 1;
        kCount -= 1;
        return old;
    }

    @Override
    @SuppressWarnings("unchecked")
    public V remove (Object key) { return delete ((K) key); }
    
//-----------------------------------------------------------------------------------
// Print/show the B+Tree
//-----------------------------------------------------------------------------------

    /********************************************************************************
     * Show/print this B+Tree.
     */
    void show ()
    {
        out.println ("BpTreeMap");
        printT (root, 0);
        out.println ("-".repeat (60));
    } // show

    /********************************************************************************
     * Print the B+Tree using a pre-order traversal and indenting each level.
     * @param n      the current node to print
     * @param level  the current level of the B+Tree
     */
    @SuppressWarnings("unchecked")
    private void printT (Node n, int level)
    {
        if (n != null) {
            out.println ("\t".repeat (level) + n);
            if (! n.isLeaf)
                for (var j = 0; j <= n.keys; j++) printT ((Node) n.ref[j], level + 1);
        } // if
    } // printT

//-----------------------------------------------------------------------------------
// Main method for running/testing the B+Tree
//-----------------------------------------------------------------------------------

    /********************************************************************************
     * The main method used for testing.  Also test for more keys and with RANDOMLY true.
     * @param  the command-line arguments (args[0] gives number of keys to insert)
     */
    public static void main (String [] args)
    {
        var totalKeys = 30;                    
        var RANDOMLY  = false;
        var rng       = new Random ();
        var bpt       = new BpTreeMap <Integer, Integer> (Integer.class, Integer.class);
        if (args.length == 1) totalKeys = Integer.valueOf (args[0]);
   
        if (RANDOMLY)
            for (var i = 1; i <= totalKeys; i += 2) bpt.put (rng.nextInt (2 * totalKeys), i * i);
        else
            for (var i = 1; i <= totalKeys; i += 2) bpt.put (i, i * i);

        bpt.printT (bpt.root, 0);
        for (var i = 0; i <= totalKeys; i++)
            out.println ("key = " + i + ", value = " + bpt.get (i));
        out.println ("-------------------------------------------");
        out.println ("number of keys in BpTree = " + bpt.kCount);
        out.println ("-------------------------------------------");
        out.println ("Average number of nodes accessed = " + bpt.count / (double) totalKeys);

        int expectedSize = (totalKeys + 1) / 2;
        assert bpt.size () == expectedSize : "Size mismatch";
        for (var i = 1; i <= 13; i += 2) {
            assert bpt.get (i) != null && bpt.get (i).equals (i * i) : "Incorrect value for " + i;
        }
        for (var i = 0; i <= totalKeys; i += 2) {
            assert bpt.get (i) == null : "Unexpected value for " + i;
        }
    } // main

} // BpTreeMap

