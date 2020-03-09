// By default, a function is ghost, and cannot be called from non-ghost code.  To make it non-ghost, replace the keyword function with the two keywords “function method”.
// http://homepage.cs.uiowa.edu/~tinelli/classes/181/Papers/dafny-reference.pdf pg 76

class {:autocontracts} CarPark 
{
    // Log messages
    const debug := true;

    // Total car park size
    const carParkSize:= 20;

    // Minimum number of empty spaces
    const minEmptySpaces:= 5;

    // Number of reserved spaces - 0 by default
    const reservedSpacesSize:= 5;

    // The current number of subscriptions
    var subscriptionCount : int

    // Array of vehicle registrations with subscription
    var subscriptionRegistrations: seq<int>;

    // If reserved parking in force, true by default
    var reservedParkingInForce: bool;
    
    // IDs of public available spaces
    var availableSpaces: set<int>;

    // IDs of reserved spaces
    var reservedSpaces: set<int>;
    
    // IDs of in use spaces
    var inUseSpaces: set<int>;

    // Set car park size
    constructor ()
    // Ensure sets are correct size
    ensures |inUseSpaces| == 0; 
    ensures |reservedSpaces| == reservedSpacesSize;
    ensures |availableSpaces| == carParkSize - reservedSpacesSize;
    ensures subscriptionCount == 0;
    ensures |subscriptionRegistrations| == 0;
    ensures reservedParkingInForce;
    {
        this.subscriptionRegistrations:= [];
        this.subscriptionCount:= 0;
        this.reservedParkingInForce:= true;
        // Hard coding set values as cardinality won't work with set comprehension
        // https://stackoverflow.com/a/48989897/10789835
        this.inUseSpaces:= {};
        this.reservedSpaces:= {0,1,2,3,4};
        this.availableSpaces:= {5,6,7,8,9,10,11,12,13,14,15,16,17,18,19};
    }

    method printSets()
    {
        print "inUseSpaces: ", this.inUseSpaces, "\n";
        print "reservedSpaces: ", this.reservedSpaces, "\n";
        print "availableSpaces: ", this.availableSpaces, "\n";
    }

    method enterCarPark() returns (spaceId: int, success: bool)
    modifies this;
    // If failes:
    // Should be as not enough spaces, and ensure no changes made
    ensures old(|availableSpaces|) <= minEmptySpaces ==> !success;
    ensures !success ==> old(inUseSpaces) == inUseSpaces && old(availableSpaces) == availableSpaces;
    // If success:
    // check spaceId wasn't already in use, and that no other changes made to old set
    ensures success ==> spaceId !in old(inUseSpaces) && old(inUseSpaces) + {spaceId} == inUseSpaces;
    // Check spaceId was available old, and no other changes made to availableSpaces
    ensures success ==> spaceId in old(availableSpaces) && old(availableSpaces) == availableSpaces + {spaceId};
    // Check reserved set not changed regardless
    ensures old(reservedSpaces) == reservedSpaces;
    // autocontract ensures spaceId doesn't exist in more than one set
    {
        // Check if enough empty spaces or return early
        if |availableSpaces| <= minEmptySpaces
        {
            spaceId := -1;
            success := false;
            if debug { print "enterCarPark - availableSpaces less than minEmptySpaces \n"; }
            return;
        }

        // Get an arbitrary id and set success
        spaceId :| spaceId in availableSpaces;
        success := true;

        // Remove spaceId from availableSpaces and add to inUseSpaces
        availableSpaces := availableSpaces - {spaceId};
        inUseSpaces := inUseSpaces + {spaceId};

        if debug { print "enterCarPark - space ", spaceId, "\n"; }

    } 

    method leaveCarPark(spaceId: int) returns (success: bool)
    modifies this;
    // If no success:
    // If spaceId not in old inUse, then should have failed
    ensures spaceId !in old(inUseSpaces) ==> !success;
    // All sets should remain the same
    ensures !success ==> 
        old(inUseSpaces) == inUseSpaces && 
        old(availableSpaces) == availableSpaces && 
        old(reservedSpaces) == reservedSpaces;
    // If success:
    // If success, spaceId should be in old inUseSpaces, but not after and no other changes
    ensures success ==> 
        spaceId in old(inUseSpaces) && 
        spaceId !in inUseSpaces && 
        old(inUseSpaces) == inUseSpaces + {spaceId};
    // If spaceId was reserved space and reservedInForce, spaceId should now be in reservedSpaces with no other changes
    ensures success && reservedParkingInForce && spaceId < reservedSpacesSize ==>
        spaceId !in old(reservedSpaces) &&
        old(reservedSpaces) + {spaceId} == reservedSpaces;
    // If spaceId was not in reserved space, or !reservedParkingInForce, should now be in availableSpaces with no other changes
    ensures success && ((spaceId > reservedSpacesSize) || !reservedParkingInForce) ==> 
        spaceId !in old (availableSpaces) &&
        old(availableSpaces) + {spaceId} == availableSpaces;
    // Precontract enforces correct set length and no duplication
    {
        // If not inUse, fail early
        if (spaceId !in inUseSpaces) 
        {
            success := false;
            if debug { print "leaveCarPark(",spaceId,") - failed, spaceId not in use\n"; }
            return;
        }

        success := true;
        inUseSpaces := inUseSpaces - {spaceId};
        if debug { print "leaveCarPark(",spaceId,") - success\n"; }

        // Check if weekend parking and early return
        if (!reservedParkingInForce)
        {
            availableSpaces := availableSpaces + {spaceId};
            return;
        }

        // Check if space should be returned to reserved parking or not
        if (spaceId < reservedSpacesSize)
        {
            reservedSpaces := reservedSpaces + {spaceId};
        }
        else
        {
            availableSpaces := availableSpaces + {spaceId};
        }
    }

    function checkAvailability(): int
    {
       |availableSpaces| - minEmptySpaces
    }

    // Returns if available spaces greater than minEmptySpaces
    // Needs to be function method to allow use in method body
    function method hasAvailableSpaces(): bool
    {
        |availableSpaces| > minEmptySpaces
    }

    // Return if given reg is subscribed to reserved parking
    // Needs to be function method to allow use in method body
    function method regSubscribed(reg: int): bool
    {
        // Convert array to sequence for ease of checking
        reg in subscriptionRegistrations[..]
    }

    method enterReservedCarPark(registration: int) returns (spaceId: int, success: bool)
    modifies this;
    // If no success in any case, make sure all sets remain unchanged
    ensures !success ==> 
        old(inUseSpaces) == inUseSpaces && 
        old(reservedSpaces) == reservedSpaces && 
        old(availableSpaces) == availableSpaces;
    // If reserved in force:
    // Reject if not a subscriber
    ensures reservedParkingInForce && !regSubscribed(registration) ==> !success;
    // If registered and some reserved spaces available, return success
    ensures reservedParkingInForce && regSubscribed(registration) && |old(reservedSpaces)| > 0 ==> success;
    // Check spaceId was in old(reservedSpaces) but now removed and no other changes
    // Check spaceId wasn't in old(inUseSpaces) but now is with no other changes
    // Check no changes to available spaces
    ensures reservedParkingInForce && success ==> 
        spaceId in old(reservedSpaces) && 
        old(reservedSpaces) - {spaceId} == reservedSpaces &&
        spaceId !in old(inUseSpaces) &&
        old(inUseSpaces) + {spaceId} == inUseSpaces && 
        old(availableSpaces) == availableSpaces;
    // If reserved not in force:
    // If no spaces, should fail - need to check old predicate to check value before set size may be modified
    ensures !reservedParkingInForce && old(!hasAvailableSpaces()) ==> !success;
    ensures !reservedParkingInForce && old(hasAvailableSpaces()) ==> success;
    // Check old(availableSpaces) had spaceId but doesn't now, that inUseSpaces didn't have it but now does and no changes to reserved
    ensures !reservedParkingInForce && success ==> 
        spaceId in old(availableSpaces) &&
        old(availableSpaces) - {spaceId} == availableSpaces &&
        spaceId !in old(inUseSpaces) && 
        inUseSpaces == old(inUseSpaces) + {spaceId} && 
        old(reservedSpaces) == reservedSpaces;
    {
        // Check if registration is allowed (convert array to sequence for easy checking)
        if reservedParkingInForce && !regSubscribed(registration)
        {
            spaceId := -1;
            success := false;
            if debug { print "enterReservedCarPark(",registration,") - reg not subscribed\n"; }
            return;
        }

        // If reserve in force and reg subscribed (need assert |reservedSpaces| > 0 for :| assignment) 
        if reservedParkingInForce && |reservedSpaces| > 0 && regSubscribed(registration)
        {
            spaceId :| spaceId in reservedSpaces;
            reservedSpaces := reservedSpaces - {spaceId};
            inUseSpaces := inUseSpaces + {spaceId};
            success := true;
            if debug { print "enterReservedCarPark(",registration,") - reg in allowed list. Returning spaceID ", spaceId,"\n";}
            return;
        }
        
        
        // If reserved parking not in force but no available space
        if !reservedParkingInForce && !hasAvailableSpaces()
        {
            spaceId := -1;
            success := false;
            if debug { print "enterReservedCarPark(",registration,") - reservedParking not in force but no avail spaces";}
            return;
        }

        // If reservedParking not in force and we have available space
        if !reservedParkingInForce && hasAvailableSpaces()
        {
            spaceId :| spaceId in availableSpaces;
            availableSpaces := availableSpaces - {spaceId};
            inUseSpaces := inUseSpaces + {spaceId};
            success := true;
            if debug { print "enterReservedCarPark(",registration,") - reservedParking not in force. Returning spaceID ", spaceId,"\n";}
            return;
        }

        // Shouldn't get here
        spaceId := -1;
        success := false;
        if debug { print "enterReservedCarPark(",registration,") - unknown error - not caught by conditions";}
    }

    method makeSubscription(registration: int) returns (success: bool)
    modifies this;
    // Ensure in any case that sets haven't changed
    ensures 
        old(availableSpaces) == availableSpaces && 
        old(inUseSpaces) == inUseSpaces && 
        old(reservedSpaces) == reservedSpaces;
    // If failed, subscriptions should not have changed
    ensures !success ==> 
        old(subscriptionRegistrations) == subscriptionRegistrations &&
        old(subscriptionCount) == subscriptionCount;
    // If no room, should fail
    ensures old(subscriptionCount) >= reservedSpacesSize ==> !success;
    // If already registered, should fail
    ensures registration in old(subscriptionRegistrations[..]) ==> !success;
    // If room in array and unique, should pass
    ensures old(subscriptionCount) < reservedSpacesSize && registration !in old(subscriptionRegistrations[..]) ==> 
        success;
    // If pass, check array updated and counter incremented
    ensures success ==> 
        registration !in old(subscriptionRegistrations[..]) && 
        registration in subscriptionRegistrations[..] && 
        subscriptionCount == old(subscriptionCount) + 1 &&
        old(subscriptionRegistrations[..] + [registration]) == subscriptionRegistrations[..];
    {
        // Check space available
        if subscriptionCount >= reservedSpacesSize
        {
            success := false;
            if debug { print "makeSubscription() - subscriptions full, rejected\n";}
            return;
        }

        // Check reg not already subscribed
        if (registration in subscriptionRegistrations[..])
        {
            success := false;
            if debug { print "makeSubscription() - reg already subscribed, rejected\n";}
            return;
        }

        // Make subscription
        subscriptionRegistrations := subscriptionRegistrations + [registration];
        subscriptionCount := subscriptionCount + 1;
        success := true;
        if debug { print "makeSubscription() - reg", registration, "subscribed \n";}
        return;
    }

    method openReservedArea()
    modifies this;
    // make sure inUse not modified
    ensures old(inUseSpaces) == inUseSpaces;
    ensures !reservedParkingInForce;
    // availableSpaces size should be total of old(availableSpaces) + old(reservedSpaces)
    ensures |availableSpaces| == old(|availableSpaces|) + old(|reservedSpaces|);
    ensures availableSpaces == old(availableSpaces) + old(reservedSpaces);
    // Check reservedSpaces now empty
    ensures |reservedSpaces| == 0;
    {    
        // Update flag
        reservedParkingInForce := false;

        // Move all reserved spaces to available
        availableSpaces := availableSpaces + reservedSpaces;
        reservedSpaces:= {};
        if debug {print "openReservedArea() - done";}
    }

    method closeCarPark() returns (destroyed: int)
    modifies this;
    ensures old(|inUseSpaces|) == destroyed;
    ensures inUseSpaces == {};
    ensures |reservedSpaces| == 5;
    ensures |availableSpaces| == 15;
    ensures reservedParkingInForce;
    {
        destroyed := |inUseSpaces|;
        
        // Reset state
        inUseSpaces := {};
        reservedSpaces := {0,1,2,3,4};
        availableSpaces := {5,6,7,8,9,10,11,12,13,14,15,16,17,18,19};  
        reservedParkingInForce := true;
        if debug { print "closeCarPark() - carpark closed. ", destroyed, " cars destroyed"; }
    }

    // For overall car park state
    predicate Valid()
    reads this;
    {
        // Ensure no values appear in both given sets
        availableSpaces * inUseSpaces == {} &&
        reservedSpaces * inUseSpaces == {} &&
        availableSpaces * reservedSpaces == {} &&
        // Ensure total size of sets == overall car park size
        |availableSpaces| + |inUseSpaces| + |reservedSpaces| == carParkSize &&
        // Ensure subscription count always between 0 and array length
        0 <= subscriptionCount <= reservedSpacesSize &&
        // Ensure all values in sets are within 0 to carParkSize(20)
        forall i :: i in (availableSpaces + reservedSpaces + inUseSpaces) ==> 0 <= i < carParkSize
    }


    // Needs setting to read only ??
    method printStatus()
    {
        var output := "";

        // for loop (i in carParkSize)
        // if availableSpaces.has(i) {output = output + i + "A  "}
        // if reservedSpaces.has(i) {output = output + i + "R  "}
        // if inUseSpaces.has(i) {output = output + i + "X  "}

        // total available reserved = |reservedSpaces|
        // total available public = |availableSpaces|
        // total spaces in use = |inUseSpaces|
        
    }
}

method Main()
{
    var cp := new CarPark();
    cp.printSets();

    var id1, success1 := cp.enterCarPark();
    var id2, success2 := cp.enterCarPark();
    var id3, success3 := cp.enterCarPark();
    var id4, success4 := cp.enterCarPark();
    var id5, success5 := cp.enterCarPark();
    var id6, success6 := cp.enterCarPark();

    cp.printSets();     

    var leaveSuccess := cp.leaveCarPark(id1);
  
    var re1, successRes1 := cp.enterReservedCarPark(1);

    var regSuccess := cp.makeSubscription(1);

    re1, successRes1 := cp.enterReservedCarPark(1);

    leaveSuccess := cp.leaveCarPark(re1);

    var re2, successRes2 := cp.enterReservedCarPark(2);

    cp.openReservedArea();

    re2, successRes2 := cp.enterReservedCarPark(2);

    cp.printSets();

}