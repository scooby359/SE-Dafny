class {:valid} CarPark {

    // Total car park size
    var carParkSize: int;

    // Minimum number of empty spaces - set to 5 in constructor
    var minEmptySpaces: int;

    // Number of reserved spaces - 0 by default
    var reservedSpacesSize: int; // int

    // The current number of subscriptions
    var currentSubscriptionCount : int

    // Array of vehicle registrations with subscription
    var subscriptionRegistrations: array<int>;

    // If reserved parking in force, true by default
    var reservedParkingInForce: bool;
    
    // IDs of public available spaces
    var availableSpaces: set<int>;

    // IDs of reserved spaces
    var reservedSpaces: set<int>;
    
    // IDs of in use spaces
    var inUseSpaces: set<int>;


    // Set car park size
    constructor (carParkSize: int, reservedSpacesSize: int) {
        this.carParkSize:= carParkSize;
        this.reservedSpacesSize:= reservedSpacesSize;
        this.minEmptySpaces:= 5;
        this.subscriptionRegistrations:= new int[this.reservedSpacesSize];
        this.currentSubscriptionCount:= 0;
        this.reservedParkingInForce:= true;
        this.inUseSpaces:= new set<int>;
        this.reservedSpaces:= new set<int>;
        this.availableSpaces:= new set<int>;

        // Need to initialise set values (dafny docs down, can't find out how)
        // reserved spaces == 1..reservedSpacedSize
        // available spaces == (reservedSpacesSize + 1)..carParkSize
    }

    method enterCarPark() 
    {
        // If |availableSpace| < minEmptySpaces
        // Return fail (-1?)

        // space = Get availableSpace.random
        // availableSpace - space
        // inUseSpaces + space
        // return space number

    } 

    method leaveCarPark(spaceId: int) 
    {
        // Take space number as input param
        // availableSpace - spaceId
        // if (spaceId <= reservedSpacesSize ) 
        //      reservedSpaces + spaceId
        // else
        //      availableSpaces + spaceId
    }

    // Should be a function - won't change anything, just return value
    function checkAvailability() : int 
    {
        // return |availableSpaces|
    }

    method enterReservedCarPark(registration: int) {

        // if reservedParkingInForce && registration not in subscriptionRegistrations
        //      return fail (-1);

        // if reserved parkingInForce && registration in subscriptionRegistrations
        //      spaceId = reservedSpaces.random
        //      reservedSpaces - spaceId
        //      inUseSpaces + spaceId
        //      return spaceId

        // if !parkingInForce
        //      spaceId = availableSpaces.random
        //      availableSpaces - spaceId
        //      inUseSpaces + spaceId
        //      return spaceId

    }

    method makeSubscription(registration: int) {
        // Check space available
        // if subscriptionCount => reservedSpacesSize
        //      return false (fail?)

        // subscriptionRegistrations[subscriptionCount] = registration
        // subscriptionCount++
        // return true
    }

    method openReservedArea() {
        // reservedParkingInForce = false;
        // availableSpaces + reservedSpaces
        // reservedSpaces = {}

    }

    method closeCarPark() {
        // carsDestroyed = |inUseSpaces|
        // Reset state
        // inUseSpaces = {}
        // reservedSpaces = {1...numberOfReservedSpaces}
        // availableSpaces = {(numberOfReservedSpaces + 1) ... carParkSize}
        // return carsDestroyed
    }

    // For overall car park state
    predicate valid()
        reads this
    {
        this.availableSpaces * this.inUseSpaces == {} &&
        this.reservedSpaces * this.inUseSpaces == {} &&
        this.availableSpaces * this.reservedSpaces == {} && 
        |this.availableSpaces| + |this.inUseSpaces| + |this.reservedSpaces| == carParkSize &&
        carParkSize > 0
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
